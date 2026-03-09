// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Balancing
// Imports: public import Init.Data.Ord.Basic public import Std.Data.DTreeMap.Internal.Balanced import Init.ByCases import Init.Data.Nat.Lemmas import Init.Data.Nat.Simproc import Init.Omega
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
static const lean_string_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DTreeMap"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Impl"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__3_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tacticTree_tac"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__4_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 108, 102, 221, 169, 83, 94, 148)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 90, 101, 118, 142, 120, 198, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value_aux_3),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__4_value),LEAN_SCALAR_PTR_LITERAL(156, 209, 254, 216, 210, 30, 88, 47)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tree_tac"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__7_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__8_value;
LEAN_EXPORT const lean_object* l_Std_DTreeMap_Internal_Impl_tacticTree__tac = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__8_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__10 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__10_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "substEqs"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__12 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__12_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(202, 114, 170, 89, 111, 248, 44, 200)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "subst_eqs"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__14 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__14_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repeat'"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__16 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__16_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(199, 67, 182, 138, 186, 187, 207, 59)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__18 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__18_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(104, 58, 38, 157, 113, 69, 9, 24)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__20 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__20_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__22 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__22_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__23 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__23_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__25 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__25_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__26 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__26_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__28 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__28_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__30 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__30_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__31 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__31_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__32 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__32_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Internal.tree_tac"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__34 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__34_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__2_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6_value),LEAN_SCALAR_PTR_LITERAL(243, 155, 163, 92, 201, 101, 200, 86)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__37 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__37_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__38 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__38_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__40 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__40_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__41 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__41_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(134, 218, 71, 35, 220, 118, 132, 17)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__43 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__43_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticRepeat_"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__44 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__44_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(149, 101, 42, 245, 144, 172, 68, 230)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__46 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__46_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__47 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__47_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(197, 49, 98, 208, 150, 151, 163, 74)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimTarget"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__49 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__49_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(136, 63, 46, 91, 99, 29, 205, 171)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term‹_›"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__51 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__51_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(149, 139, 117, 210, 91, 226, 103, 115)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__52 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__52_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "‹"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__53 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__53_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∧_"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__54 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__54_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(213, 224, 85, 99, 168, 124, 84, 223)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__55 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__55_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__56 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__56_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__57 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__57_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__59 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__59_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∧"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__60 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__60_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "›"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__61 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__61_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__62 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__62_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "And.intro"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__64 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__64_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__66 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__66_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__67 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__67_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__69 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__69_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__70 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__70_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__71 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__71_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "contradiction"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__73 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__73_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(112, 219, 21, 122, 229, 107, 49, 36)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__75 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__75_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__77 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__77_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term✓"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term_u2713___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 108, 102, 221, 169, 83, 94, 148)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 90, 101, 118, 142, 120, 198, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value_aux_3),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 243, 125, 162, 36, 42, 37, 216)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "✓"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term_u2713___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__2_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__2_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term_u2713___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term_u2713___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__3_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term_u2713___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_DTreeMap_Internal_Impl_term_u2713 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term_u2713___closed__4_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "as_aux_lemma"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(248, 107, 244, 71, 211, 100, 179, 147)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__5_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4;
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.DTreeMap.Internal.Impl.balance!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "balance! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__34));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__64));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
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
x_13 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4));
x_14 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__5));
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7));
x_17 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9));
x_18 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11));
x_19 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13));
x_20 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__14));
lean_inc(x_12);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_12);
x_22 = l_Lean_Syntax_node1(x_12, x_19, x_21);
x_23 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15);
lean_inc(x_12);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_23);
x_25 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__16));
x_26 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17));
lean_inc(x_12);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_25);
x_28 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__18));
x_29 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19));
lean_inc(x_12);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_28);
lean_inc_ref_n(x_24, 2);
lean_inc(x_12);
x_31 = l_Lean_Syntax_node3(x_12, x_29, x_30, x_24, x_24);
lean_inc(x_12);
x_32 = l_Lean_Syntax_node1(x_12, x_18, x_31);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node1(x_12, x_17, x_32);
lean_inc(x_12);
x_34 = l_Lean_Syntax_node1(x_12, x_16, x_33);
lean_inc_ref(x_27);
lean_inc(x_12);
x_35 = l_Lean_Syntax_node2(x_12, x_26, x_27, x_34);
x_36 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21));
x_37 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__22));
lean_inc(x_12);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_37);
x_39 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24));
x_40 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__25));
lean_inc(x_12);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_40);
x_42 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__26));
x_43 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27));
lean_inc(x_12);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_42);
x_45 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29));
lean_inc_ref(x_24);
lean_inc(x_12);
x_46 = l_Lean_Syntax_node1(x_12, x_45, x_24);
x_47 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__30));
lean_inc(x_12);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_18, x_48);
x_50 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__31));
lean_inc(x_12);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_50);
x_52 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33));
x_53 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35);
x_54 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36));
lean_inc(x_9);
lean_inc(x_8);
x_55 = l_Lean_addMacroScope(x_8, x_54, x_9);
x_56 = lean_box(0);
lean_inc(x_12);
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_12);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
lean_inc_ref_n(x_24, 2);
lean_inc(x_12);
x_58 = l_Lean_Syntax_node3(x_12, x_52, x_24, x_24, x_57);
lean_inc(x_12);
x_59 = l_Lean_Syntax_node1(x_12, x_18, x_58);
x_60 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__37));
lean_inc(x_12);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_12);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node3(x_12, x_18, x_51, x_59, x_61);
x_63 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39));
x_64 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__40));
lean_inc(x_12);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_12);
lean_ctor_set(x_65, 1, x_64);
x_66 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42));
x_67 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__43));
lean_inc(x_12);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_12);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node1(x_12, x_66, x_68);
lean_inc(x_12);
x_70 = l_Lean_Syntax_node2(x_12, x_63, x_65, x_69);
lean_inc(x_12);
x_71 = l_Lean_Syntax_node1(x_12, x_18, x_70);
lean_inc_ref(x_24);
lean_inc(x_46);
lean_inc(x_12);
x_72 = l_Lean_Syntax_node6(x_12, x_43, x_44, x_46, x_24, x_49, x_62, x_71);
lean_inc(x_12);
x_73 = l_Lean_Syntax_node1(x_12, x_18, x_72);
lean_inc(x_12);
x_74 = l_Lean_Syntax_node1(x_12, x_17, x_73);
lean_inc(x_12);
x_75 = l_Lean_Syntax_node1(x_12, x_16, x_74);
lean_inc_ref(x_41);
lean_inc(x_12);
x_76 = l_Lean_Syntax_node2(x_12, x_39, x_41, x_75);
lean_inc(x_76);
lean_inc(x_12);
x_77 = l_Lean_Syntax_node1(x_12, x_18, x_76);
lean_inc(x_12);
x_78 = l_Lean_Syntax_node1(x_12, x_17, x_77);
lean_inc(x_12);
x_79 = l_Lean_Syntax_node1(x_12, x_16, x_78);
lean_inc_ref(x_38);
lean_inc(x_12);
x_80 = l_Lean_Syntax_node2(x_12, x_36, x_38, x_79);
x_81 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45));
x_82 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__46));
lean_inc(x_12);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_82);
x_84 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__47));
x_85 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48));
lean_inc(x_12);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_12);
lean_ctor_set(x_86, 1, x_84);
x_87 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50));
x_88 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__52));
x_89 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__53));
lean_inc(x_12);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_89);
x_91 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__55));
x_92 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58));
x_93 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__59));
lean_inc(x_12);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_12);
lean_ctor_set(x_94, 1, x_93);
lean_inc(x_12);
x_95 = l_Lean_Syntax_node1(x_12, x_92, x_94);
x_96 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__60));
lean_inc(x_12);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_12);
lean_ctor_set(x_97, 1, x_96);
lean_inc(x_95);
lean_inc(x_12);
x_98 = l_Lean_Syntax_node3(x_12, x_91, x_95, x_97, x_95);
x_99 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__61));
lean_inc(x_12);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_12);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_12);
x_101 = l_Lean_Syntax_node3(x_12, x_88, x_90, x_98, x_100);
lean_inc_ref(x_24);
lean_inc(x_12);
x_102 = l_Lean_Syntax_node2(x_12, x_87, x_24, x_101);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node1(x_12, x_18, x_102);
lean_inc_ref_n(x_24, 2);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node4(x_12, x_85, x_86, x_103, x_24, x_24);
lean_inc(x_12);
x_105 = l_Lean_Syntax_node1(x_12, x_18, x_104);
lean_inc(x_12);
x_106 = l_Lean_Syntax_node1(x_12, x_17, x_105);
lean_inc(x_12);
x_107 = l_Lean_Syntax_node1(x_12, x_16, x_106);
lean_inc(x_12);
x_108 = l_Lean_Syntax_node2(x_12, x_81, x_83, x_107);
x_109 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__62));
x_110 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63));
lean_inc(x_12);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_12);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65);
x_113 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68));
x_114 = l_Lean_addMacroScope(x_8, x_113, x_9);
x_115 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__70));
lean_inc(x_12);
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_12);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_114);
lean_ctor_set(x_116, 3, x_115);
lean_inc(x_12);
x_117 = l_Lean_Syntax_node2(x_12, x_110, x_111, x_116);
lean_inc(x_12);
x_118 = l_Lean_Syntax_node1(x_12, x_18, x_117);
lean_inc(x_12);
x_119 = l_Lean_Syntax_node1(x_12, x_17, x_118);
lean_inc(x_12);
x_120 = l_Lean_Syntax_node1(x_12, x_16, x_119);
lean_inc(x_12);
x_121 = l_Lean_Syntax_node2(x_12, x_26, x_27, x_120);
lean_inc_ref_n(x_24, 2);
lean_inc(x_12);
x_122 = l_Lean_Syntax_node5(x_12, x_18, x_76, x_24, x_108, x_24, x_121);
lean_inc(x_12);
x_123 = l_Lean_Syntax_node1(x_12, x_17, x_122);
lean_inc(x_12);
x_124 = l_Lean_Syntax_node1(x_12, x_16, x_123);
lean_inc_ref(x_38);
lean_inc(x_12);
x_125 = l_Lean_Syntax_node2(x_12, x_36, x_38, x_124);
x_126 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__71));
x_127 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72));
lean_inc(x_12);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_12);
lean_ctor_set(x_128, 1, x_126);
lean_inc(x_12);
x_129 = l_Lean_Syntax_node1(x_12, x_127, x_128);
lean_inc(x_12);
x_130 = l_Lean_Syntax_node1(x_12, x_18, x_129);
lean_inc(x_12);
x_131 = l_Lean_Syntax_node1(x_12, x_17, x_130);
lean_inc(x_12);
x_132 = l_Lean_Syntax_node1(x_12, x_16, x_131);
lean_inc_ref(x_41);
lean_inc(x_12);
x_133 = l_Lean_Syntax_node2(x_12, x_39, x_41, x_132);
x_134 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__73));
x_135 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74));
lean_inc(x_12);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_12);
lean_ctor_set(x_136, 1, x_134);
lean_inc(x_12);
x_137 = l_Lean_Syntax_node1(x_12, x_135, x_136);
lean_inc(x_12);
x_138 = l_Lean_Syntax_node1(x_12, x_18, x_137);
lean_inc(x_12);
x_139 = l_Lean_Syntax_node1(x_12, x_17, x_138);
lean_inc(x_12);
x_140 = l_Lean_Syntax_node1(x_12, x_16, x_139);
lean_inc(x_12);
x_141 = l_Lean_Syntax_node2(x_12, x_39, x_41, x_140);
lean_inc_ref(x_24);
lean_inc(x_12);
x_142 = l_Lean_Syntax_node3(x_12, x_18, x_133, x_24, x_141);
lean_inc(x_12);
x_143 = l_Lean_Syntax_node1(x_12, x_17, x_142);
lean_inc(x_12);
x_144 = l_Lean_Syntax_node1(x_12, x_16, x_143);
lean_inc_ref(x_38);
lean_inc(x_12);
x_145 = l_Lean_Syntax_node2(x_12, x_36, x_38, x_144);
x_146 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__75));
x_147 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76));
lean_inc(x_12);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_12);
lean_ctor_set(x_148, 1, x_146);
lean_inc(x_12);
x_149 = l_Lean_Syntax_node2(x_12, x_147, x_148, x_46);
lean_inc_ref(x_24);
lean_inc(x_22);
lean_inc(x_12);
x_150 = l_Lean_Syntax_node3(x_12, x_18, x_22, x_24, x_149);
lean_inc(x_12);
x_151 = l_Lean_Syntax_node1(x_12, x_17, x_150);
lean_inc(x_12);
x_152 = l_Lean_Syntax_node1(x_12, x_16, x_151);
lean_inc(x_12);
x_153 = l_Lean_Syntax_node2(x_12, x_36, x_38, x_152);
x_154 = lean_unsigned_to_nat(12u);
x_155 = lean_mk_empty_array_with_capacity(x_154);
x_156 = lean_array_push(x_155, x_22);
lean_inc_ref(x_24);
x_157 = lean_array_push(x_156, x_24);
x_158 = lean_array_push(x_157, x_35);
lean_inc_ref(x_24);
x_159 = lean_array_push(x_158, x_24);
x_160 = lean_array_push(x_159, x_80);
lean_inc_ref(x_24);
x_161 = lean_array_push(x_160, x_24);
x_162 = lean_array_push(x_161, x_125);
lean_inc_ref(x_24);
x_163 = lean_array_push(x_162, x_24);
x_164 = lean_array_push(x_163, x_145);
lean_inc_ref(x_24);
x_165 = lean_array_push(x_164, x_24);
x_166 = lean_array_push(x_165, x_153);
x_167 = lean_array_push(x_166, x_24);
lean_inc(x_12);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_12);
lean_ctor_set(x_168, 1, x_18);
lean_ctor_set(x_168, 2, x_167);
lean_inc(x_12);
x_169 = l_Lean_Syntax_node1(x_12, x_17, x_168);
lean_inc(x_12);
x_170 = l_Lean_Syntax_node1(x_12, x_16, x_169);
x_171 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__77));
lean_inc(x_12);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_12);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_Syntax_node3(x_12, x_13, x_15, x_170, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_3);
return x_174;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1));
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1));
x_12 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__2));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7));
x_15 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9));
x_16 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11));
x_17 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__3));
x_18 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4));
lean_inc(x_10);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
x_20 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__5));
lean_inc(x_10);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5));
x_23 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6));
lean_inc(x_10);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_10);
x_25 = l_Lean_Syntax_node1(x_10, x_22, x_24);
lean_inc(x_10);
x_26 = l_Lean_Syntax_node1(x_10, x_16, x_25);
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_15, x_26);
lean_inc(x_10);
x_28 = l_Lean_Syntax_node1(x_10, x_14, x_27);
lean_inc(x_10);
x_29 = l_Lean_Syntax_node3(x_10, x_18, x_19, x_21, x_28);
lean_inc(x_10);
x_30 = l_Lean_Syntax_node1(x_10, x_16, x_29);
lean_inc(x_10);
x_31 = l_Lean_Syntax_node1(x_10, x_15, x_30);
lean_inc(x_10);
x_32 = l_Lean_Syntax_node1(x_10, x_14, x_31);
x_33 = l_Lean_Syntax_node2(x_10, x_11, x_13, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_mul(x_11, x_5);
x_13 = lean_nat_dec_lt(x_12, x_6);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_14, x_6);
x_16 = lean_nat_add(x_15, x_5);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_83; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_83 = !lean_is_exclusive(x_3);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_3, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_3, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_3, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_3, 0);
lean_dec(x_88);
x_18 = x_3;
x_19 = x_83;
goto block_82;
}
else
{
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
x_24 = lean_ctor_get(x_10, 3);
x_25 = lean_ctor_get(x_10, 4);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_mul(x_26, x_20);
x_28 = lean_nat_dec_lt(x_21, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_56; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_56 = !lean_is_exclusive(x_10);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_10, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_10, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_10, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_10, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_10, 0);
lean_dec(x_61);
x_29 = x_10;
x_30 = x_56;
goto block_55;
}
else
{
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; lean_object* x_46; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_31, x_6);
lean_dec(x_6);
x_33 = lean_nat_add(x_32, x_5);
lean_dec(x_32);
x_45 = lean_nat_add(x_31, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_24, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_44:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_4);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 2, x_2);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 0, x_37);
x_38 = x_29;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_2);
lean_ctor_set(x_43, 3, x_25);
lean_ctor_set(x_43, 4, x_4);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_38);
lean_ctor_set(x_18, 3, x_35);
lean_ctor_set(x_18, 2, x_23);
lean_ctor_set(x_18, 1, x_22);
lean_ctor_set(x_18, 0, x_33);
x_39 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set(x_41, 2, x_23);
lean_ctor_set(x_41, 3, x_35);
lean_ctor_set(x_41, 4, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
lean_ctor_set(x_48, 2, x_8);
lean_ctor_set(x_48, 3, x_9);
lean_ctor_set(x_48, 4, x_24);
x_49 = lean_nat_add(x_31, x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_34 = x_49;
x_35 = x_48;
x_36 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_34 = x_49;
x_35 = x_48;
x_36 = x_51;
goto block_44;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_62, x_6);
lean_dec(x_6);
x_64 = lean_nat_add(x_63, x_5);
lean_dec(x_63);
x_65 = lean_nat_add(x_62, x_5);
x_66 = lean_nat_add(x_65, x_21);
lean_dec(x_65);
lean_inc_ref(x_4);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_4);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 0, x_66);
x_67 = x_18;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_1);
lean_ctor_set(x_81, 2, x_2);
lean_ctor_set(x_81, 3, x_10);
lean_ctor_set(x_81, 4, x_4);
x_67 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_68; uint8_t x_69; uint8_t x_74; 
x_74 = !lean_is_exclusive(x_4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_4, 4);
lean_dec(x_75);
x_76 = lean_ctor_get(x_4, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_4, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_4, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_4, 0);
lean_dec(x_79);
x_68 = x_4;
x_69 = x_74;
goto block_73;
}
else
{
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 3, x_9);
lean_ctor_set(x_68, 2, x_8);
lean_ctor_set(x_68, 1, x_7);
lean_ctor_set(x_68, 0, x_64);
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_7);
lean_ctor_set(x_72, 2, x_8);
lean_ctor_set(x_72, 3, x_9);
lean_ctor_set(x_72, 4, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_4, 0);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_90, x_89);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_1);
lean_ctor_set(x_92, 2, x_2);
lean_ctor_set(x_92, 3, x_3);
lean_ctor_set(x_92, 4, x_4);
return x_92;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_106; 
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_3, 4);
x_95 = lean_ctor_get(x_3, 1);
x_96 = lean_ctor_get(x_3, 2);
x_106 = !lean_is_exclusive(x_3);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_3, 3);
lean_dec(x_107);
x_108 = lean_ctor_get(x_3, 0);
lean_dec(x_108);
x_97 = x_3;
x_98 = x_106;
goto block_105;
}
else
{
lean_inc(x_94);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_3);
x_97 = lean_box(0);
x_98 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_unsigned_to_nat(1u);
lean_inc(x_94);
if (x_98 == 0)
{
lean_ctor_set(x_97, 3, x_94);
lean_ctor_set(x_97, 2, x_2);
lean_ctor_set(x_97, 1, x_1);
lean_ctor_set(x_97, 0, x_100);
x_101 = x_97;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_1);
lean_ctor_set(x_104, 2, x_2);
lean_ctor_set(x_104, 3, x_94);
lean_ctor_set(x_104, 4, x_94);
x_101 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_95);
lean_ctor_set(x_102, 2, x_96);
lean_ctor_set(x_102, 3, x_93);
lean_ctor_set(x_102, 4, x_101);
return x_102;
}
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_3, 4);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_133; 
lean_inc(x_93);
x_110 = lean_ctor_get(x_3, 1);
x_111 = lean_ctor_get(x_3, 2);
x_133 = !lean_is_exclusive(x_3);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_3, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_3, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_3, 0);
lean_dec(x_136);
x_112 = x_3;
x_113 = x_133;
goto block_132;
}
else
{
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_3);
x_112 = lean_box(0);
x_113 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_128; 
x_114 = lean_ctor_get(x_109, 1);
x_115 = lean_ctor_get(x_109, 2);
x_128 = !lean_is_exclusive(x_109);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_109, 4);
lean_dec(x_129);
x_130 = lean_ctor_get(x_109, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_109, 0);
lean_dec(x_131);
x_116 = x_109;
x_117 = x_128;
goto block_127;
}
else
{
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_109);
x_116 = lean_box(0);
x_117 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_unsigned_to_nat(3u);
x_119 = lean_unsigned_to_nat(1u);
if (x_117 == 0)
{
lean_ctor_set(x_116, 4, x_93);
lean_ctor_set(x_116, 3, x_93);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 1, x_110);
lean_ctor_set(x_116, 0, x_119);
x_120 = x_116;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_110);
lean_ctor_set(x_126, 2, x_111);
lean_ctor_set(x_126, 3, x_93);
lean_ctor_set(x_126, 4, x_93);
x_120 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_121; 
if (x_113 == 0)
{
lean_ctor_set(x_112, 4, x_93);
lean_ctor_set(x_112, 2, x_2);
lean_ctor_set(x_112, 1, x_1);
lean_ctor_set(x_112, 0, x_119);
x_121 = x_112;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_1);
lean_ctor_set(x_124, 2, x_2);
lean_ctor_set(x_124, 3, x_93);
lean_ctor_set(x_124, 4, x_93);
x_121 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_115);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_121);
return x_122;
}
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_unsigned_to_nat(2u);
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_1);
lean_ctor_set(x_138, 2, x_2);
lean_ctor_set(x_138, 3, x_3);
lean_ctor_set(x_138, 4, x_109);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_1);
lean_ctor_set(x_140, 2, x_2);
lean_ctor_set(x_140, 3, x_3);
lean_ctor_set(x_140, 4, x_3);
return x_140;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_mul(x_16, x_10);
x_18 = lean_nat_dec_lt(x_17, x_11);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_19, x_11);
x_21 = lean_nat_add(x_20, x_10);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_5);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; uint8_t x_88; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_88 = !lean_is_exclusive(x_5);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_5, 4);
lean_dec(x_89);
x_90 = lean_ctor_get(x_5, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_5, 2);
lean_dec(x_91);
x_92 = lean_ctor_get(x_5, 1);
lean_dec(x_92);
x_93 = lean_ctor_get(x_5, 0);
lean_dec(x_93);
x_23 = x_5;
x_24 = x_88;
goto block_87;
}
else
{
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
x_28 = lean_ctor_get(x_15, 2);
x_29 = lean_ctor_get(x_15, 3);
x_30 = lean_ctor_get(x_15, 4);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_mul(x_31, x_25);
x_33 = lean_nat_dec_lt(x_26, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_61; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_61 = !lean_is_exclusive(x_15);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_15, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_15, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_15, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_15, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_15, 0);
lean_dec(x_66);
x_34 = x_15;
x_35 = x_61;
goto block_60;
}
else
{
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; lean_object* x_51; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_36, x_11);
lean_dec(x_11);
x_38 = lean_nat_add(x_37, x_10);
lean_dec(x_37);
x_50 = lean_nat_add(x_36, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_29, 0);
lean_inc(x_58);
x_51 = x_58;
goto block_57;
}
else
{
lean_object* x_59; 
x_59 = lean_unsigned_to_nat(0u);
x_51 = x_59;
goto block_57;
}
block_49:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_nat_add(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_6);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 2, x_4);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 0, x_42);
x_43 = x_34;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_3);
lean_ctor_set(x_48, 2, x_4);
lean_ctor_set(x_48, 3, x_30);
lean_ctor_set(x_48, 4, x_6);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_43);
lean_ctor_set(x_23, 3, x_40);
lean_ctor_set(x_23, 2, x_28);
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_38);
x_44 = x_23;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_27);
lean_ctor_set(x_46, 2, x_28);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
block_57:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_nat_add(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_12);
lean_ctor_set(x_53, 2, x_13);
lean_ctor_set(x_53, 3, x_14);
lean_ctor_set(x_53, 4, x_29);
x_54 = lean_nat_add(x_36, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_30, 0);
lean_inc(x_55);
x_39 = x_54;
x_40 = x_53;
x_41 = x_55;
goto block_49;
}
else
{
lean_object* x_56; 
x_56 = lean_unsigned_to_nat(0u);
x_39 = x_54;
x_40 = x_53;
x_41 = x_56;
goto block_49;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_67, x_11);
lean_dec(x_11);
x_69 = lean_nat_add(x_68, x_10);
lean_dec(x_68);
x_70 = lean_nat_add(x_67, x_10);
x_71 = lean_nat_add(x_70, x_26);
lean_dec(x_70);
lean_inc_ref(x_6);
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_6);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 0, x_71);
x_72 = x_23;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_3);
lean_ctor_set(x_86, 2, x_4);
lean_ctor_set(x_86, 3, x_15);
lean_ctor_set(x_86, 4, x_6);
x_72 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_73; uint8_t x_74; uint8_t x_79; 
x_79 = !lean_is_exclusive(x_6);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_6, 4);
lean_dec(x_80);
x_81 = lean_ctor_get(x_6, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_6, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_6, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_6, 0);
lean_dec(x_84);
x_73 = x_6;
x_74 = x_79;
goto block_78;
}
else
{
lean_dec(x_6);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 3, x_14);
lean_ctor_set(x_73, 2, x_13);
lean_ctor_set(x_73, 1, x_12);
lean_ctor_set(x_73, 0, x_69);
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_12);
lean_ctor_set(x_77, 2, x_13);
lean_ctor_set(x_77, 3, x_14);
lean_ctor_set(x_77, 4, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_6, 0);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_94);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_3);
lean_ctor_set(x_97, 2, x_4);
lean_ctor_set(x_97, 3, x_5);
lean_ctor_set(x_97, 4, x_6);
return x_97;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_111; 
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_5, 4);
x_100 = lean_ctor_get(x_5, 1);
x_101 = lean_ctor_get(x_5, 2);
x_111 = !lean_is_exclusive(x_5);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_5, 3);
lean_dec(x_112);
x_113 = lean_ctor_get(x_5, 0);
lean_dec(x_113);
x_102 = x_5;
x_103 = x_111;
goto block_110;
}
else
{
lean_inc(x_99);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_5);
x_102 = lean_box(0);
x_103 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_unsigned_to_nat(3u);
x_105 = lean_unsigned_to_nat(1u);
lean_inc(x_99);
if (x_103 == 0)
{
lean_ctor_set(x_102, 3, x_99);
lean_ctor_set(x_102, 2, x_4);
lean_ctor_set(x_102, 1, x_3);
lean_ctor_set(x_102, 0, x_105);
x_106 = x_102;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_3);
lean_ctor_set(x_109, 2, x_4);
lean_ctor_set(x_109, 3, x_99);
lean_ctor_set(x_109, 4, x_99);
x_106 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_101);
lean_ctor_set(x_107, 3, x_98);
lean_ctor_set(x_107, 4, x_106);
return x_107;
}
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_5, 4);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_138; 
lean_inc(x_98);
x_115 = lean_ctor_get(x_5, 1);
x_116 = lean_ctor_get(x_5, 2);
x_138 = !lean_is_exclusive(x_5);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_5, 4);
lean_dec(x_139);
x_140 = lean_ctor_get(x_5, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_5, 0);
lean_dec(x_141);
x_117 = x_5;
x_118 = x_138;
goto block_137;
}
else
{
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_5);
x_117 = lean_box(0);
x_118 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_133; 
x_119 = lean_ctor_get(x_114, 1);
x_120 = lean_ctor_get(x_114, 2);
x_133 = !lean_is_exclusive(x_114);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_114, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_114, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_114, 0);
lean_dec(x_136);
x_121 = x_114;
x_122 = x_133;
goto block_132;
}
else
{
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_114);
x_121 = lean_box(0);
x_122 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_unsigned_to_nat(1u);
if (x_122 == 0)
{
lean_ctor_set(x_121, 4, x_98);
lean_ctor_set(x_121, 3, x_98);
lean_ctor_set(x_121, 2, x_116);
lean_ctor_set(x_121, 1, x_115);
lean_ctor_set(x_121, 0, x_124);
x_125 = x_121;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_124);
lean_ctor_set(x_131, 1, x_115);
lean_ctor_set(x_131, 2, x_116);
lean_ctor_set(x_131, 3, x_98);
lean_ctor_set(x_131, 4, x_98);
x_125 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_126; 
if (x_118 == 0)
{
lean_ctor_set(x_117, 4, x_98);
lean_ctor_set(x_117, 2, x_4);
lean_ctor_set(x_117, 1, x_3);
lean_ctor_set(x_117, 0, x_124);
x_126 = x_117;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_3);
lean_ctor_set(x_129, 2, x_4);
lean_ctor_set(x_129, 3, x_98);
lean_ctor_set(x_129, 4, x_98);
x_126 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_125);
lean_ctor_set(x_127, 4, x_126);
return x_127;
}
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_unsigned_to_nat(2u);
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
lean_ctor_set(x_143, 2, x_4);
lean_ctor_set(x_143, 3, x_5);
lean_ctor_set(x_143, 4, x_114);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_3);
lean_ctor_set(x_145, 2, x_4);
lean_ctor_set(x_145, 3, x_5);
lean_ctor_set(x_145, 4, x_5);
return x_145;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_mul(x_11, x_5);
x_13 = lean_nat_dec_lt(x_12, x_6);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_14, x_6);
x_16 = lean_nat_add(x_15, x_5);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_83; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_83 = !lean_is_exclusive(x_3);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_3, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_3, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_3, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_3, 0);
lean_dec(x_88);
x_18 = x_3;
x_19 = x_83;
goto block_82;
}
else
{
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
x_24 = lean_ctor_get(x_10, 3);
x_25 = lean_ctor_get(x_10, 4);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_mul(x_26, x_20);
x_28 = lean_nat_dec_lt(x_21, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_56; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_56 = !lean_is_exclusive(x_10);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_10, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_10, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_10, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_10, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_10, 0);
lean_dec(x_61);
x_29 = x_10;
x_30 = x_56;
goto block_55;
}
else
{
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; lean_object* x_46; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_31, x_6);
lean_dec(x_6);
x_33 = lean_nat_add(x_32, x_5);
lean_dec(x_32);
x_45 = lean_nat_add(x_31, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_24, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_44:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_4);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 2, x_2);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 0, x_37);
x_38 = x_29;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_2);
lean_ctor_set(x_43, 3, x_25);
lean_ctor_set(x_43, 4, x_4);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_38);
lean_ctor_set(x_18, 3, x_34);
lean_ctor_set(x_18, 2, x_23);
lean_ctor_set(x_18, 1, x_22);
lean_ctor_set(x_18, 0, x_33);
x_39 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set(x_41, 2, x_23);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
lean_ctor_set(x_48, 2, x_8);
lean_ctor_set(x_48, 3, x_9);
lean_ctor_set(x_48, 4, x_24);
x_49 = lean_nat_add(x_31, x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_34 = x_48;
x_35 = x_49;
x_36 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_34 = x_48;
x_35 = x_49;
x_36 = x_51;
goto block_44;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_62, x_6);
lean_dec(x_6);
x_64 = lean_nat_add(x_63, x_5);
lean_dec(x_63);
x_65 = lean_nat_add(x_62, x_5);
x_66 = lean_nat_add(x_65, x_21);
lean_dec(x_65);
lean_inc_ref(x_4);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_4);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 0, x_66);
x_67 = x_18;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_1);
lean_ctor_set(x_81, 2, x_2);
lean_ctor_set(x_81, 3, x_10);
lean_ctor_set(x_81, 4, x_4);
x_67 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_68; uint8_t x_69; uint8_t x_74; 
x_74 = !lean_is_exclusive(x_4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_4, 4);
lean_dec(x_75);
x_76 = lean_ctor_get(x_4, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_4, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_4, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_4, 0);
lean_dec(x_79);
x_68 = x_4;
x_69 = x_74;
goto block_73;
}
else
{
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 3, x_9);
lean_ctor_set(x_68, 2, x_8);
lean_ctor_set(x_68, 1, x_7);
lean_ctor_set(x_68, 0, x_64);
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_7);
lean_ctor_set(x_72, 2, x_8);
lean_ctor_set(x_72, 3, x_9);
lean_ctor_set(x_72, 4, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_4, 0);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_90, x_89);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_1);
lean_ctor_set(x_92, 2, x_2);
lean_ctor_set(x_92, 3, x_3);
lean_ctor_set(x_92, 4, x_4);
return x_92;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_3, 4);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_120; 
x_95 = lean_ctor_get(x_3, 0);
x_96 = lean_ctor_get(x_3, 1);
x_97 = lean_ctor_get(x_3, 2);
x_120 = !lean_is_exclusive(x_3);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_3, 4);
lean_dec(x_121);
x_122 = lean_ctor_get(x_3, 3);
lean_dec(x_122);
x_98 = x_3;
x_99 = x_120;
goto block_119;
}
else
{
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_3);
x_98 = lean_box(0);
x_99 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_94, 0);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_add(x_101, x_95);
lean_dec(x_95);
x_103 = lean_nat_add(x_101, x_100);
lean_inc_ref(x_94);
if (x_99 == 0)
{
lean_ctor_set(x_98, 4, x_4);
lean_ctor_set(x_98, 3, x_94);
lean_ctor_set(x_98, 2, x_2);
lean_ctor_set(x_98, 1, x_1);
lean_ctor_set(x_98, 0, x_103);
x_104 = x_98;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_118, 0, x_103);
lean_ctor_set(x_118, 1, x_1);
lean_ctor_set(x_118, 2, x_2);
lean_ctor_set(x_118, 3, x_94);
lean_ctor_set(x_118, 4, x_4);
x_104 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_105; uint8_t x_106; uint8_t x_111; 
x_111 = !lean_is_exclusive(x_94);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_94, 4);
lean_dec(x_112);
x_113 = lean_ctor_get(x_94, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_94, 2);
lean_dec(x_114);
x_115 = lean_ctor_get(x_94, 1);
lean_dec(x_115);
x_116 = lean_ctor_get(x_94, 0);
lean_dec(x_116);
x_105 = x_94;
x_106 = x_111;
goto block_110;
}
else
{
lean_dec(x_94);
x_105 = lean_box(0);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_104);
lean_ctor_set(x_105, 3, x_93);
lean_ctor_set(x_105, 2, x_97);
lean_ctor_set(x_105, 1, x_96);
lean_ctor_set(x_105, 0, x_102);
x_107 = x_105;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_96);
lean_ctor_set(x_109, 2, x_97);
lean_ctor_set(x_109, 3, x_93);
lean_ctor_set(x_109, 4, x_104);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_134; 
x_123 = lean_ctor_get(x_3, 1);
x_124 = lean_ctor_get(x_3, 2);
x_134 = !lean_is_exclusive(x_3);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_3, 4);
lean_dec(x_135);
x_136 = lean_ctor_get(x_3, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_3, 0);
lean_dec(x_137);
x_125 = x_3;
x_126 = x_134;
goto block_133;
}
else
{
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_3);
x_125 = lean_box(0);
x_126 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_unsigned_to_nat(3u);
x_128 = lean_unsigned_to_nat(1u);
if (x_126 == 0)
{
lean_ctor_set(x_125, 3, x_94);
lean_ctor_set(x_125, 2, x_2);
lean_ctor_set(x_125, 1, x_1);
lean_ctor_set(x_125, 0, x_128);
x_129 = x_125;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_1);
lean_ctor_set(x_132, 2, x_2);
lean_ctor_set(x_132, 3, x_94);
lean_ctor_set(x_132, 4, x_94);
x_129 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_123);
lean_ctor_set(x_130, 2, x_124);
lean_ctor_set(x_130, 3, x_93);
lean_ctor_set(x_130, 4, x_129);
return x_130;
}
}
}
}
else
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_3, 4);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_162; 
lean_inc(x_93);
x_139 = lean_ctor_get(x_3, 1);
x_140 = lean_ctor_get(x_3, 2);
x_162 = !lean_is_exclusive(x_3);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_3, 4);
lean_dec(x_163);
x_164 = lean_ctor_get(x_3, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_3, 0);
lean_dec(x_165);
x_141 = x_3;
x_142 = x_162;
goto block_161;
}
else
{
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_3);
x_141 = lean_box(0);
x_142 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_157; 
x_143 = lean_ctor_get(x_138, 1);
x_144 = lean_ctor_get(x_138, 2);
x_157 = !lean_is_exclusive(x_138);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_138, 4);
lean_dec(x_158);
x_159 = lean_ctor_get(x_138, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_138, 0);
lean_dec(x_160);
x_145 = x_138;
x_146 = x_157;
goto block_156;
}
else
{
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_138);
x_145 = lean_box(0);
x_146 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_unsigned_to_nat(3u);
x_148 = lean_unsigned_to_nat(1u);
if (x_146 == 0)
{
lean_ctor_set(x_145, 4, x_93);
lean_ctor_set(x_145, 3, x_93);
lean_ctor_set(x_145, 2, x_140);
lean_ctor_set(x_145, 1, x_139);
lean_ctor_set(x_145, 0, x_148);
x_149 = x_145;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_139);
lean_ctor_set(x_155, 2, x_140);
lean_ctor_set(x_155, 3, x_93);
lean_ctor_set(x_155, 4, x_93);
x_149 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_150; 
if (x_142 == 0)
{
lean_ctor_set(x_141, 4, x_93);
lean_ctor_set(x_141, 2, x_2);
lean_ctor_set(x_141, 1, x_1);
lean_ctor_set(x_141, 0, x_148);
x_150 = x_141;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_1);
lean_ctor_set(x_153, 2, x_2);
lean_ctor_set(x_153, 3, x_93);
lean_ctor_set(x_153, 4, x_93);
x_150 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_144);
lean_ctor_set(x_151, 3, x_149);
lean_ctor_set(x_151, 4, x_150);
return x_151;
}
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_unsigned_to_nat(2u);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_1);
lean_ctor_set(x_167, 2, x_2);
lean_ctor_set(x_167, 3, x_3);
lean_ctor_set(x_167, 4, x_138);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_1);
lean_ctor_set(x_169, 2, x_2);
lean_ctor_set(x_169, 3, x_3);
lean_ctor_set(x_169, 4, x_3);
return x_169;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_mul(x_16, x_10);
x_18 = lean_nat_dec_lt(x_17, x_11);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_19, x_11);
x_21 = lean_nat_add(x_20, x_10);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_5);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; uint8_t x_88; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_88 = !lean_is_exclusive(x_5);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_5, 4);
lean_dec(x_89);
x_90 = lean_ctor_get(x_5, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_5, 2);
lean_dec(x_91);
x_92 = lean_ctor_get(x_5, 1);
lean_dec(x_92);
x_93 = lean_ctor_get(x_5, 0);
lean_dec(x_93);
x_23 = x_5;
x_24 = x_88;
goto block_87;
}
else
{
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
x_28 = lean_ctor_get(x_15, 2);
x_29 = lean_ctor_get(x_15, 3);
x_30 = lean_ctor_get(x_15, 4);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_mul(x_31, x_25);
x_33 = lean_nat_dec_lt(x_26, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_61; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_61 = !lean_is_exclusive(x_15);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_15, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_15, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_15, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_15, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_15, 0);
lean_dec(x_66);
x_34 = x_15;
x_35 = x_61;
goto block_60;
}
else
{
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; lean_object* x_51; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_36, x_11);
lean_dec(x_11);
x_38 = lean_nat_add(x_37, x_10);
lean_dec(x_37);
x_50 = lean_nat_add(x_36, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_29, 0);
lean_inc(x_58);
x_51 = x_58;
goto block_57;
}
else
{
lean_object* x_59; 
x_59 = lean_unsigned_to_nat(0u);
x_51 = x_59;
goto block_57;
}
block_49:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_6);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 2, x_4);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 0, x_42);
x_43 = x_34;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_3);
lean_ctor_set(x_48, 2, x_4);
lean_ctor_set(x_48, 3, x_30);
lean_ctor_set(x_48, 4, x_6);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_43);
lean_ctor_set(x_23, 3, x_39);
lean_ctor_set(x_23, 2, x_28);
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_38);
x_44 = x_23;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_27);
lean_ctor_set(x_46, 2, x_28);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
block_57:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_nat_add(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_12);
lean_ctor_set(x_53, 2, x_13);
lean_ctor_set(x_53, 3, x_14);
lean_ctor_set(x_53, 4, x_29);
x_54 = lean_nat_add(x_36, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_30, 0);
lean_inc(x_55);
x_39 = x_53;
x_40 = x_54;
x_41 = x_55;
goto block_49;
}
else
{
lean_object* x_56; 
x_56 = lean_unsigned_to_nat(0u);
x_39 = x_53;
x_40 = x_54;
x_41 = x_56;
goto block_49;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_67, x_11);
lean_dec(x_11);
x_69 = lean_nat_add(x_68, x_10);
lean_dec(x_68);
x_70 = lean_nat_add(x_67, x_10);
x_71 = lean_nat_add(x_70, x_26);
lean_dec(x_70);
lean_inc_ref(x_6);
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_6);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 0, x_71);
x_72 = x_23;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_3);
lean_ctor_set(x_86, 2, x_4);
lean_ctor_set(x_86, 3, x_15);
lean_ctor_set(x_86, 4, x_6);
x_72 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_73; uint8_t x_74; uint8_t x_79; 
x_79 = !lean_is_exclusive(x_6);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_6, 4);
lean_dec(x_80);
x_81 = lean_ctor_get(x_6, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_6, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_6, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_6, 0);
lean_dec(x_84);
x_73 = x_6;
x_74 = x_79;
goto block_78;
}
else
{
lean_dec(x_6);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 3, x_14);
lean_ctor_set(x_73, 2, x_13);
lean_ctor_set(x_73, 1, x_12);
lean_ctor_set(x_73, 0, x_69);
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_12);
lean_ctor_set(x_77, 2, x_13);
lean_ctor_set(x_77, 3, x_14);
lean_ctor_set(x_77, 4, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_6, 0);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_95, x_94);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_3);
lean_ctor_set(x_97, 2, x_4);
lean_ctor_set(x_97, 3, x_5);
lean_ctor_set(x_97, 4, x_6);
return x_97;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_5, 4);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_125; 
x_100 = lean_ctor_get(x_5, 0);
x_101 = lean_ctor_get(x_5, 1);
x_102 = lean_ctor_get(x_5, 2);
x_125 = !lean_is_exclusive(x_5);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_5, 4);
lean_dec(x_126);
x_127 = lean_ctor_get(x_5, 3);
lean_dec(x_127);
x_103 = x_5;
x_104 = x_125;
goto block_124;
}
else
{
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_5);
x_103 = lean_box(0);
x_104 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_99, 0);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_106, x_100);
lean_dec(x_100);
x_108 = lean_nat_add(x_106, x_105);
lean_inc_ref(x_99);
if (x_104 == 0)
{
lean_ctor_set(x_103, 4, x_6);
lean_ctor_set(x_103, 3, x_99);
lean_ctor_set(x_103, 2, x_4);
lean_ctor_set(x_103, 1, x_3);
lean_ctor_set(x_103, 0, x_108);
x_109 = x_103;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_108);
lean_ctor_set(x_123, 1, x_3);
lean_ctor_set(x_123, 2, x_4);
lean_ctor_set(x_123, 3, x_99);
lean_ctor_set(x_123, 4, x_6);
x_109 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_110; uint8_t x_111; uint8_t x_116; 
x_116 = !lean_is_exclusive(x_99);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_99, 4);
lean_dec(x_117);
x_118 = lean_ctor_get(x_99, 3);
lean_dec(x_118);
x_119 = lean_ctor_get(x_99, 2);
lean_dec(x_119);
x_120 = lean_ctor_get(x_99, 1);
lean_dec(x_120);
x_121 = lean_ctor_get(x_99, 0);
lean_dec(x_121);
x_110 = x_99;
x_111 = x_116;
goto block_115;
}
else
{
lean_dec(x_99);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
lean_ctor_set(x_110, 4, x_109);
lean_ctor_set(x_110, 3, x_98);
lean_ctor_set(x_110, 2, x_102);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 0, x_107);
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_101);
lean_ctor_set(x_114, 2, x_102);
lean_ctor_set(x_114, 3, x_98);
lean_ctor_set(x_114, 4, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_139; 
x_128 = lean_ctor_get(x_5, 1);
x_129 = lean_ctor_get(x_5, 2);
x_139 = !lean_is_exclusive(x_5);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_5, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_5, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_5, 0);
lean_dec(x_142);
x_130 = x_5;
x_131 = x_139;
goto block_138;
}
else
{
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_5);
x_130 = lean_box(0);
x_131 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_unsigned_to_nat(3u);
x_133 = lean_unsigned_to_nat(1u);
if (x_131 == 0)
{
lean_ctor_set(x_130, 3, x_99);
lean_ctor_set(x_130, 2, x_4);
lean_ctor_set(x_130, 1, x_3);
lean_ctor_set(x_130, 0, x_133);
x_134 = x_130;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_99);
lean_ctor_set(x_137, 4, x_99);
x_134 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_128);
lean_ctor_set(x_135, 2, x_129);
lean_ctor_set(x_135, 3, x_98);
lean_ctor_set(x_135, 4, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_5, 4);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_167; 
lean_inc(x_98);
x_144 = lean_ctor_get(x_5, 1);
x_145 = lean_ctor_get(x_5, 2);
x_167 = !lean_is_exclusive(x_5);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_5, 4);
lean_dec(x_168);
x_169 = lean_ctor_get(x_5, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_5, 0);
lean_dec(x_170);
x_146 = x_5;
x_147 = x_167;
goto block_166;
}
else
{
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_5);
x_146 = lean_box(0);
x_147 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_162; 
x_148 = lean_ctor_get(x_143, 1);
x_149 = lean_ctor_get(x_143, 2);
x_162 = !lean_is_exclusive(x_143);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_143, 4);
lean_dec(x_163);
x_164 = lean_ctor_get(x_143, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_143, 0);
lean_dec(x_165);
x_150 = x_143;
x_151 = x_162;
goto block_161;
}
else
{
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_143);
x_150 = lean_box(0);
x_151 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_unsigned_to_nat(3u);
x_153 = lean_unsigned_to_nat(1u);
if (x_151 == 0)
{
lean_ctor_set(x_150, 4, x_98);
lean_ctor_set(x_150, 3, x_98);
lean_ctor_set(x_150, 2, x_145);
lean_ctor_set(x_150, 1, x_144);
lean_ctor_set(x_150, 0, x_153);
x_154 = x_150;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_144);
lean_ctor_set(x_160, 2, x_145);
lean_ctor_set(x_160, 3, x_98);
lean_ctor_set(x_160, 4, x_98);
x_154 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_155; 
if (x_147 == 0)
{
lean_ctor_set(x_146, 4, x_98);
lean_ctor_set(x_146, 2, x_4);
lean_ctor_set(x_146, 1, x_3);
lean_ctor_set(x_146, 0, x_153);
x_155 = x_146;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_3);
lean_ctor_set(x_158, 2, x_4);
lean_ctor_set(x_158, 3, x_98);
lean_ctor_set(x_158, 4, x_98);
x_155 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_148);
lean_ctor_set(x_156, 2, x_149);
lean_ctor_set(x_156, 3, x_154);
lean_ctor_set(x_156, 4, x_155);
return x_156;
}
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_unsigned_to_nat(2u);
x_172 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_3);
lean_ctor_set(x_172, 2, x_4);
lean_ctor_set(x_172, 3, x_5);
lean_ctor_set(x_172, 4, x_143);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_3);
lean_ctor_set(x_174, 2, x_4);
lean_ctor_set(x_174, 3, x_5);
lean_ctor_set(x_174, 4, x_5);
return x_174;
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2));
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(182u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(183u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_mul(x_11, x_5);
x_13 = lean_nat_dec_lt(x_12, x_6);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_14, x_6);
x_16 = lean_nat_add(x_15, x_5);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_89; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_3, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_3, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_3, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_3, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_3, 0);
lean_dec(x_94);
x_18 = x_3;
x_19 = x_89;
goto block_88;
}
else
{
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
x_24 = lean_ctor_get(x_10, 3);
x_25 = lean_ctor_get(x_10, 4);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_mul(x_26, x_20);
x_28 = lean_nat_dec_lt(x_21, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_56; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_56 = !lean_is_exclusive(x_10);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_10, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_10, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_10, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_10, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_10, 0);
lean_dec(x_61);
x_29 = x_10;
x_30 = x_56;
goto block_55;
}
else
{
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; lean_object* x_46; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_31, x_6);
lean_dec(x_6);
x_33 = lean_nat_add(x_32, x_5);
lean_dec(x_32);
x_45 = lean_nat_add(x_31, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_24, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_44:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_4);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 2, x_2);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 0, x_37);
x_38 = x_29;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_2);
lean_ctor_set(x_43, 3, x_25);
lean_ctor_set(x_43, 4, x_4);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_38);
lean_ctor_set(x_18, 3, x_34);
lean_ctor_set(x_18, 2, x_23);
lean_ctor_set(x_18, 1, x_22);
lean_ctor_set(x_18, 0, x_33);
x_39 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set(x_41, 2, x_23);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
lean_ctor_set(x_48, 2, x_8);
lean_ctor_set(x_48, 3, x_9);
lean_ctor_set(x_48, 4, x_24);
x_49 = lean_nat_add(x_31, x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_34 = x_48;
x_35 = x_49;
x_36 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_34 = x_48;
x_35 = x_49;
x_36 = x_51;
goto block_44;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_62, x_6);
lean_dec(x_6);
x_64 = lean_nat_add(x_63, x_5);
lean_dec(x_63);
x_65 = lean_nat_add(x_62, x_5);
x_66 = lean_nat_add(x_65, x_21);
lean_dec(x_65);
lean_inc_ref(x_4);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_4);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 0, x_66);
x_67 = x_18;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_1);
lean_ctor_set(x_81, 2, x_2);
lean_ctor_set(x_81, 3, x_10);
lean_ctor_set(x_81, 4, x_4);
x_67 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_68; uint8_t x_69; uint8_t x_74; 
x_74 = !lean_is_exclusive(x_4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_4, 4);
lean_dec(x_75);
x_76 = lean_ctor_get(x_4, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_4, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_4, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_4, 0);
lean_dec(x_79);
x_68 = x_4;
x_69 = x_74;
goto block_73;
}
else
{
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 3, x_9);
lean_ctor_set(x_68, 2, x_8);
lean_ctor_set(x_68, 1, x_7);
lean_ctor_set(x_68, 0, x_64);
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_7);
lean_ctor_set(x_72, 2, x_8);
lean_ctor_set(x_72, 3, x_9);
lean_ctor_set(x_72, 4, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_9);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_box(1);
x_83 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
x_84 = l_panic___redArg(x_82, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_del_object(x_18);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(1);
x_86 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
x_87 = l_panic___redArg(x_85, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_4, 0);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_96, x_95);
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_1);
lean_ctor_set(x_98, 2, x_2);
lean_ctor_set(x_98, 3, x_3);
lean_ctor_set(x_98, 4, x_4);
return x_98;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_3, 4);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_126; 
x_101 = lean_ctor_get(x_3, 0);
x_102 = lean_ctor_get(x_3, 1);
x_103 = lean_ctor_get(x_3, 2);
x_126 = !lean_is_exclusive(x_3);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_3, 4);
lean_dec(x_127);
x_128 = lean_ctor_get(x_3, 3);
lean_dec(x_128);
x_104 = x_3;
x_105 = x_126;
goto block_125;
}
else
{
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_3);
x_104 = lean_box(0);
x_105 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_100, 0);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_107, x_101);
lean_dec(x_101);
x_109 = lean_nat_add(x_107, x_106);
lean_inc_ref(x_100);
if (x_105 == 0)
{
lean_ctor_set(x_104, 4, x_4);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 2, x_2);
lean_ctor_set(x_104, 1, x_1);
lean_ctor_set(x_104, 0, x_109);
x_110 = x_104;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_1);
lean_ctor_set(x_124, 2, x_2);
lean_ctor_set(x_124, 3, x_100);
lean_ctor_set(x_124, 4, x_4);
x_110 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_111; uint8_t x_112; uint8_t x_117; 
x_117 = !lean_is_exclusive(x_100);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_100, 4);
lean_dec(x_118);
x_119 = lean_ctor_get(x_100, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_100, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_100, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_100, 0);
lean_dec(x_122);
x_111 = x_100;
x_112 = x_117;
goto block_116;
}
else
{
lean_dec(x_100);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
lean_ctor_set(x_111, 4, x_110);
lean_ctor_set(x_111, 3, x_99);
lean_ctor_set(x_111, 2, x_103);
lean_ctor_set(x_111, 1, x_102);
lean_ctor_set(x_111, 0, x_108);
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_102);
lean_ctor_set(x_115, 2, x_103);
lean_ctor_set(x_115, 3, x_99);
lean_ctor_set(x_115, 4, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_140; 
x_129 = lean_ctor_get(x_3, 1);
x_130 = lean_ctor_get(x_3, 2);
x_140 = !lean_is_exclusive(x_3);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_3, 4);
lean_dec(x_141);
x_142 = lean_ctor_get(x_3, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_3, 0);
lean_dec(x_143);
x_131 = x_3;
x_132 = x_140;
goto block_139;
}
else
{
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_3);
x_131 = lean_box(0);
x_132 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_unsigned_to_nat(3u);
x_134 = lean_unsigned_to_nat(1u);
if (x_132 == 0)
{
lean_ctor_set(x_131, 3, x_100);
lean_ctor_set(x_131, 2, x_2);
lean_ctor_set(x_131, 1, x_1);
lean_ctor_set(x_131, 0, x_134);
x_135 = x_131;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_1);
lean_ctor_set(x_138, 2, x_2);
lean_ctor_set(x_138, 3, x_100);
lean_ctor_set(x_138, 4, x_100);
x_135 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_129);
lean_ctor_set(x_136, 2, x_130);
lean_ctor_set(x_136, 3, x_99);
lean_ctor_set(x_136, 4, x_135);
return x_136;
}
}
}
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_3, 4);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_168; 
lean_inc(x_99);
x_145 = lean_ctor_get(x_3, 1);
x_146 = lean_ctor_get(x_3, 2);
x_168 = !lean_is_exclusive(x_3);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_3, 4);
lean_dec(x_169);
x_170 = lean_ctor_get(x_3, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_3, 0);
lean_dec(x_171);
x_147 = x_3;
x_148 = x_168;
goto block_167;
}
else
{
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_3);
x_147 = lean_box(0);
x_148 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_163; 
x_149 = lean_ctor_get(x_144, 1);
x_150 = lean_ctor_get(x_144, 2);
x_163 = !lean_is_exclusive(x_144);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_144, 4);
lean_dec(x_164);
x_165 = lean_ctor_get(x_144, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_144, 0);
lean_dec(x_166);
x_151 = x_144;
x_152 = x_163;
goto block_162;
}
else
{
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_144);
x_151 = lean_box(0);
x_152 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_unsigned_to_nat(3u);
x_154 = lean_unsigned_to_nat(1u);
if (x_152 == 0)
{
lean_ctor_set(x_151, 4, x_99);
lean_ctor_set(x_151, 3, x_99);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 0, x_154);
x_155 = x_151;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_145);
lean_ctor_set(x_161, 2, x_146);
lean_ctor_set(x_161, 3, x_99);
lean_ctor_set(x_161, 4, x_99);
x_155 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_156; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 4, x_99);
lean_ctor_set(x_147, 2, x_2);
lean_ctor_set(x_147, 1, x_1);
lean_ctor_set(x_147, 0, x_154);
x_156 = x_147;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_1);
lean_ctor_set(x_159, 2, x_2);
lean_ctor_set(x_159, 3, x_99);
lean_ctor_set(x_159, 4, x_99);
x_156 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_156);
return x_157;
}
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_1);
lean_ctor_set(x_173, 2, x_2);
lean_ctor_set(x_173, 3, x_3);
lean_ctor_set(x_173, 4, x_144);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_1);
lean_ctor_set(x_175, 2, x_2);
lean_ctor_set(x_175, 3, x_3);
lean_ctor_set(x_175, 4, x_3);
return x_175;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_ctor_get(x_5, 3);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_mul(x_13, x_7);
x_15 = lean_nat_dec_lt(x_14, x_8);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_16, x_8);
x_18 = lean_nat_add(x_17, x_7);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_5);
lean_ctor_set(x_19, 4, x_6);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_91; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_91 = !lean_is_exclusive(x_5);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_5, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_5, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_5, 2);
lean_dec(x_94);
x_95 = lean_ctor_get(x_5, 1);
lean_dec(x_95);
x_96 = lean_ctor_get(x_5, 0);
lean_dec(x_96);
x_20 = x_5;
x_21 = x_91;
goto block_90;
}
else
{
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = x_91;
goto block_90;
}
block_90:
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_mul(x_28, x_22);
x_30 = lean_nat_dec_lt(x_23, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_58; 
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_12, 4);
lean_dec(x_59);
x_60 = lean_ctor_get(x_12, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_12, 2);
lean_dec(x_61);
x_62 = lean_ctor_get(x_12, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_12, 0);
lean_dec(x_63);
x_31 = x_12;
x_32 = x_58;
goto block_57;
}
else
{
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_47; lean_object* x_48; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_33, x_8);
lean_dec(x_8);
x_35 = lean_nat_add(x_34, x_7);
lean_dec(x_34);
x_47 = lean_nat_add(x_33, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
x_48 = x_55;
goto block_54;
}
else
{
lean_object* x_56; 
x_56 = lean_unsigned_to_nat(0u);
x_48 = x_56;
goto block_54;
}
block_46:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_nat_add(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_32 == 0)
{
lean_ctor_set(x_31, 4, x_6);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 0, x_39);
x_40 = x_31;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_4);
lean_ctor_set(x_45, 3, x_27);
lean_ctor_set(x_45, 4, x_6);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 4, x_40);
lean_ctor_set(x_20, 3, x_36);
lean_ctor_set(x_20, 2, x_25);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_35);
x_41 = x_20;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_24);
lean_ctor_set(x_43, 2, x_25);
lean_ctor_set(x_43, 3, x_36);
lean_ctor_set(x_43, 4, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
block_54:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_9);
lean_ctor_set(x_50, 2, x_10);
lean_ctor_set(x_50, 3, x_11);
lean_ctor_set(x_50, 4, x_26);
x_51 = lean_nat_add(x_33, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_27, 0);
lean_inc(x_52);
x_36 = x_50;
x_37 = x_51;
x_38 = x_52;
goto block_46;
}
else
{
lean_object* x_53; 
x_53 = lean_unsigned_to_nat(0u);
x_36 = x_50;
x_37 = x_51;
x_38 = x_53;
goto block_46;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_64, x_8);
lean_dec(x_8);
x_66 = lean_nat_add(x_65, x_7);
lean_dec(x_65);
x_67 = lean_nat_add(x_64, x_7);
x_68 = lean_nat_add(x_67, x_23);
lean_dec(x_67);
lean_inc_ref(x_6);
if (x_21 == 0)
{
lean_ctor_set(x_20, 4, x_6);
lean_ctor_set(x_20, 3, x_12);
lean_ctor_set(x_20, 2, x_4);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 0, x_68);
x_69 = x_20;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_3);
lean_ctor_set(x_83, 2, x_4);
lean_ctor_set(x_83, 3, x_12);
lean_ctor_set(x_83, 4, x_6);
x_69 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_70; uint8_t x_71; uint8_t x_76; 
x_76 = !lean_is_exclusive(x_6);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_6, 4);
lean_dec(x_77);
x_78 = lean_ctor_get(x_6, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_6, 2);
lean_dec(x_79);
x_80 = lean_ctor_get(x_6, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_6, 0);
lean_dec(x_81);
x_70 = x_6;
x_71 = x_76;
goto block_75;
}
else
{
lean_dec(x_6);
x_70 = lean_box(0);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; 
if (x_71 == 0)
{
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 3, x_11);
lean_ctor_set(x_70, 2, x_10);
lean_ctor_set(x_70, 1, x_9);
lean_ctor_set(x_70, 0, x_66);
x_72 = x_70;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_9);
lean_ctor_set(x_74, 2, x_10);
lean_ctor_set(x_74, 3, x_11);
lean_ctor_set(x_74, 4, x_69);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_11);
lean_del_object(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_84 = lean_box(1);
x_85 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
x_86 = l_panic___redArg(x_84, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_del_object(x_20);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_87 = lean_box(1);
x_88 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
x_89 = l_panic___redArg(x_87, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_6, 0);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_98, x_97);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_3);
lean_ctor_set(x_100, 2, x_4);
lean_ctor_set(x_100, 3, x_5);
lean_ctor_set(x_100, 4, x_6);
return x_100;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_5, 4);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_128; 
x_103 = lean_ctor_get(x_5, 0);
x_104 = lean_ctor_get(x_5, 1);
x_105 = lean_ctor_get(x_5, 2);
x_128 = !lean_is_exclusive(x_5);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_5, 4);
lean_dec(x_129);
x_130 = lean_ctor_get(x_5, 3);
lean_dec(x_130);
x_106 = x_5;
x_107 = x_128;
goto block_127;
}
else
{
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_5);
x_106 = lean_box(0);
x_107 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_102, 0);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_add(x_109, x_103);
lean_dec(x_103);
x_111 = lean_nat_add(x_109, x_108);
lean_inc_ref(x_102);
if (x_107 == 0)
{
lean_ctor_set(x_106, 4, x_6);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 2, x_4);
lean_ctor_set(x_106, 1, x_3);
lean_ctor_set(x_106, 0, x_111);
x_112 = x_106;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_111);
lean_ctor_set(x_126, 1, x_3);
lean_ctor_set(x_126, 2, x_4);
lean_ctor_set(x_126, 3, x_102);
lean_ctor_set(x_126, 4, x_6);
x_112 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_113; uint8_t x_114; uint8_t x_119; 
x_119 = !lean_is_exclusive(x_102);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_102, 4);
lean_dec(x_120);
x_121 = lean_ctor_get(x_102, 3);
lean_dec(x_121);
x_122 = lean_ctor_get(x_102, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_102, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_102, 0);
lean_dec(x_124);
x_113 = x_102;
x_114 = x_119;
goto block_118;
}
else
{
lean_dec(x_102);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
lean_ctor_set(x_113, 4, x_112);
lean_ctor_set(x_113, 3, x_101);
lean_ctor_set(x_113, 2, x_105);
lean_ctor_set(x_113, 1, x_104);
lean_ctor_set(x_113, 0, x_110);
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_104);
lean_ctor_set(x_117, 2, x_105);
lean_ctor_set(x_117, 3, x_101);
lean_ctor_set(x_117, 4, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_142; 
x_131 = lean_ctor_get(x_5, 1);
x_132 = lean_ctor_get(x_5, 2);
x_142 = !lean_is_exclusive(x_5);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_5, 4);
lean_dec(x_143);
x_144 = lean_ctor_get(x_5, 3);
lean_dec(x_144);
x_145 = lean_ctor_get(x_5, 0);
lean_dec(x_145);
x_133 = x_5;
x_134 = x_142;
goto block_141;
}
else
{
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_5);
x_133 = lean_box(0);
x_134 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_unsigned_to_nat(3u);
x_136 = lean_unsigned_to_nat(1u);
if (x_134 == 0)
{
lean_ctor_set(x_133, 3, x_102);
lean_ctor_set(x_133, 2, x_4);
lean_ctor_set(x_133, 1, x_3);
lean_ctor_set(x_133, 0, x_136);
x_137 = x_133;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_3);
lean_ctor_set(x_140, 2, x_4);
lean_ctor_set(x_140, 3, x_102);
lean_ctor_set(x_140, 4, x_102);
x_137 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_131);
lean_ctor_set(x_138, 2, x_132);
lean_ctor_set(x_138, 3, x_101);
lean_ctor_set(x_138, 4, x_137);
return x_138;
}
}
}
}
else
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_5, 4);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_170; 
lean_inc(x_101);
x_147 = lean_ctor_get(x_5, 1);
x_148 = lean_ctor_get(x_5, 2);
x_170 = !lean_is_exclusive(x_5);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_5, 4);
lean_dec(x_171);
x_172 = lean_ctor_get(x_5, 3);
lean_dec(x_172);
x_173 = lean_ctor_get(x_5, 0);
lean_dec(x_173);
x_149 = x_5;
x_150 = x_170;
goto block_169;
}
else
{
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_5);
x_149 = lean_box(0);
x_150 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_165; 
x_151 = lean_ctor_get(x_146, 1);
x_152 = lean_ctor_get(x_146, 2);
x_165 = !lean_is_exclusive(x_146);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_146, 4);
lean_dec(x_166);
x_167 = lean_ctor_get(x_146, 3);
lean_dec(x_167);
x_168 = lean_ctor_get(x_146, 0);
lean_dec(x_168);
x_153 = x_146;
x_154 = x_165;
goto block_164;
}
else
{
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_146);
x_153 = lean_box(0);
x_154 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_unsigned_to_nat(1u);
if (x_154 == 0)
{
lean_ctor_set(x_153, 4, x_101);
lean_ctor_set(x_153, 3, x_101);
lean_ctor_set(x_153, 2, x_148);
lean_ctor_set(x_153, 1, x_147);
lean_ctor_set(x_153, 0, x_156);
x_157 = x_153;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_147);
lean_ctor_set(x_163, 2, x_148);
lean_ctor_set(x_163, 3, x_101);
lean_ctor_set(x_163, 4, x_101);
x_157 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_158; 
if (x_150 == 0)
{
lean_ctor_set(x_149, 4, x_101);
lean_ctor_set(x_149, 2, x_4);
lean_ctor_set(x_149, 1, x_3);
lean_ctor_set(x_149, 0, x_156);
x_158 = x_149;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_3);
lean_ctor_set(x_161, 2, x_4);
lean_ctor_set(x_161, 3, x_101);
lean_ctor_set(x_161, 4, x_101);
x_158 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_151);
lean_ctor_set(x_159, 2, x_152);
lean_ctor_set(x_159, 3, x_157);
lean_ctor_set(x_159, 4, x_158);
return x_159;
}
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_unsigned_to_nat(2u);
x_175 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_3);
lean_ctor_set(x_175, 2, x_4);
lean_ctor_set(x_175, 3, x_5);
lean_ctor_set(x_175, 4, x_146);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_3);
lean_ctor_set(x_177, 2, x_4);
lean_ctor_set(x_177, 3, x_5);
lean_ctor_set(x_177, 4, x_5);
return x_177;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_mul(x_11, x_5);
x_13 = lean_nat_dec_lt(x_12, x_6);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_14, x_5);
x_16 = lean_nat_add(x_15, x_6);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_81; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_81 = !lean_is_exclusive(x_4);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_4, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_4, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_4, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_4, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_4, 0);
lean_dec(x_86);
x_18 = x_4;
x_19 = x_81;
goto block_80;
}
else
{
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
x_24 = lean_ctor_get(x_9, 4);
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_mul(x_26, x_25);
x_28 = lean_nat_dec_lt(x_20, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_55; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_9, 4);
lean_dec(x_56);
x_57 = lean_ctor_get(x_9, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 0);
lean_dec(x_60);
x_29 = x_9;
x_30 = x_55;
goto block_54;
}
else
{
lean_dec(x_9);
x_29 = lean_box(0);
x_30 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_31, x_5);
x_33 = lean_nat_add(x_32, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
x_45 = x_52;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = lean_unsigned_to_nat(0u);
x_45 = x_53;
goto block_51;
}
block_44:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_10);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set(x_29, 2, x_8);
lean_ctor_set(x_29, 1, x_7);
lean_ctor_set(x_29, 0, x_37);
x_38 = x_29;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_7);
lean_ctor_set(x_43, 2, x_8);
lean_ctor_set(x_43, 3, x_24);
lean_ctor_set(x_43, 4, x_10);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_38);
lean_ctor_set(x_18, 3, x_34);
lean_ctor_set(x_18, 2, x_22);
lean_ctor_set(x_18, 1, x_21);
lean_ctor_set(x_18, 0, x_33);
x_39 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_21);
lean_ctor_set(x_41, 2, x_22);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_nat_add(x_32, x_45);
lean_dec(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_3);
lean_ctor_set(x_47, 4, x_23);
x_48 = lean_nat_add(x_31, x_25);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_24, 0);
lean_inc(x_49);
x_34 = x_47;
x_35 = x_48;
x_36 = x_49;
goto block_44;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_34 = x_47;
x_35 = x_48;
x_36 = x_50;
goto block_44;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_61, x_5);
x_63 = lean_nat_add(x_62, x_6);
lean_dec(x_6);
x_64 = lean_nat_add(x_62, x_20);
lean_dec(x_62);
lean_inc_ref(x_3);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_9);
lean_ctor_set(x_18, 3, x_3);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 0, x_64);
x_65 = x_18;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_1);
lean_ctor_set(x_79, 2, x_2);
lean_ctor_set(x_79, 3, x_3);
lean_ctor_set(x_79, 4, x_9);
x_65 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_66; uint8_t x_67; uint8_t x_72; 
x_72 = !lean_is_exclusive(x_3);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_3, 4);
lean_dec(x_73);
x_74 = lean_ctor_get(x_3, 3);
lean_dec(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_dec(x_75);
x_76 = lean_ctor_get(x_3, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_3, 0);
lean_dec(x_77);
x_66 = x_3;
x_67 = x_72;
goto block_71;
}
else
{
lean_dec(x_3);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
lean_ctor_set(x_66, 4, x_10);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 2, x_8);
lean_ctor_set(x_66, 1, x_7);
lean_ctor_set(x_66, 0, x_63);
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_7);
lean_ctor_set(x_70, 2, x_8);
lean_ctor_set(x_70, 3, x_65);
lean_ctor_set(x_70, 4, x_10);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_88, x_87);
x_90 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_1);
lean_ctor_set(x_90, 2, x_2);
lean_ctor_set(x_90, 3, x_3);
lean_ctor_set(x_90, 4, x_4);
return x_90;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_4, 3);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_116; 
x_92 = lean_ctor_get(x_4, 4);
x_93 = lean_ctor_get(x_4, 1);
x_94 = lean_ctor_get(x_4, 2);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_4, 3);
lean_dec(x_117);
x_118 = lean_ctor_get(x_4, 0);
lean_dec(x_118);
x_95 = x_4;
x_96 = x_116;
goto block_115;
}
else
{
lean_inc(x_92);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_4);
x_95 = lean_box(0);
x_96 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_111; 
x_97 = lean_ctor_get(x_91, 1);
x_98 = lean_ctor_get(x_91, 2);
x_111 = !lean_is_exclusive(x_91);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_91, 4);
lean_dec(x_112);
x_113 = lean_ctor_get(x_91, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_91, 0);
lean_dec(x_114);
x_99 = x_91;
x_100 = x_111;
goto block_110;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_box(0);
x_100 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_unsigned_to_nat(3u);
x_102 = lean_unsigned_to_nat(1u);
lean_inc_n(x_92, 2);
if (x_100 == 0)
{
lean_ctor_set(x_99, 4, x_92);
lean_ctor_set(x_99, 3, x_92);
lean_ctor_set(x_99, 2, x_2);
lean_ctor_set(x_99, 1, x_1);
lean_ctor_set(x_99, 0, x_102);
x_103 = x_99;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_1);
lean_ctor_set(x_109, 2, x_2);
lean_ctor_set(x_109, 3, x_92);
lean_ctor_set(x_109, 4, x_92);
x_103 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_104; 
lean_inc(x_92);
if (x_96 == 0)
{
lean_ctor_set(x_95, 3, x_92);
lean_ctor_set(x_95, 0, x_102);
x_104 = x_95;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_93);
lean_ctor_set(x_107, 2, x_94);
lean_ctor_set(x_107, 3, x_92);
lean_ctor_set(x_107, 4, x_92);
x_104 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_98);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_4, 4);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_131; 
x_120 = lean_ctor_get(x_4, 1);
x_121 = lean_ctor_get(x_4, 2);
x_131 = !lean_is_exclusive(x_4);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_4, 4);
lean_dec(x_132);
x_133 = lean_ctor_get(x_4, 3);
lean_dec(x_133);
x_134 = lean_ctor_get(x_4, 0);
lean_dec(x_134);
x_122 = x_4;
x_123 = x_131;
goto block_130;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_4);
x_122 = lean_box(0);
x_123 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_unsigned_to_nat(1u);
if (x_123 == 0)
{
lean_ctor_set(x_122, 4, x_91);
lean_ctor_set(x_122, 2, x_2);
lean_ctor_set(x_122, 1, x_1);
lean_ctor_set(x_122, 0, x_125);
x_126 = x_122;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_1);
lean_ctor_set(x_129, 2, x_2);
lean_ctor_set(x_129, 3, x_91);
lean_ctor_set(x_129, 4, x_91);
x_126 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_120);
lean_ctor_set(x_127, 2, x_121);
lean_ctor_set(x_127, 3, x_126);
lean_ctor_set(x_127, 4, x_119);
return x_127;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_1);
lean_ctor_set(x_136, 2, x_2);
lean_ctor_set(x_136, 3, x_119);
lean_ctor_set(x_136, 4, x_4);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_1);
lean_ctor_set(x_138, 2, x_2);
lean_ctor_set(x_138, 3, x_4);
lean_ctor_set(x_138, 4, x_4);
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_mul(x_16, x_10);
x_18 = lean_nat_dec_lt(x_17, x_11);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_19, x_10);
x_21 = lean_nat_add(x_20, x_11);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_5);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; uint8_t x_86; 
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_6, 4);
lean_dec(x_87);
x_88 = lean_ctor_get(x_6, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_6, 2);
lean_dec(x_89);
x_90 = lean_ctor_get(x_6, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_6, 0);
lean_dec(x_91);
x_23 = x_6;
x_24 = x_86;
goto block_85;
}
else
{
lean_dec(x_6);
x_23 = lean_box(0);
x_24 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_mul(x_31, x_30);
x_33 = lean_nat_dec_lt(x_25, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_60; 
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_60 = !lean_is_exclusive(x_14);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_14, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_14, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_14, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_14, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_14, 0);
lean_dec(x_65);
x_34 = x_14;
x_35 = x_60;
goto block_59;
}
else
{
lean_dec(x_14);
x_34 = lean_box(0);
x_35 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_36, x_10);
x_38 = lean_nat_add(x_37, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_28, 0);
lean_inc(x_57);
x_50 = x_57;
goto block_56;
}
else
{
lean_object* x_58; 
x_58 = lean_unsigned_to_nat(0u);
x_50 = x_58;
goto block_56;
}
block_49:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_15);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_13);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 0, x_42);
x_43 = x_34;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_12);
lean_ctor_set(x_48, 2, x_13);
lean_ctor_set(x_48, 3, x_29);
lean_ctor_set(x_48, 4, x_15);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_43);
lean_ctor_set(x_23, 3, x_39);
lean_ctor_set(x_23, 2, x_27);
lean_ctor_set(x_23, 1, x_26);
lean_ctor_set(x_23, 0, x_38);
x_44 = x_23;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_26);
lean_ctor_set(x_46, 2, x_27);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
block_56:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_nat_add(x_37, x_50);
lean_dec(x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 2, x_4);
lean_ctor_set(x_52, 3, x_5);
lean_ctor_set(x_52, 4, x_28);
x_53 = lean_nat_add(x_36, x_30);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
x_39 = x_52;
x_40 = x_53;
x_41 = x_54;
goto block_49;
}
else
{
lean_object* x_55; 
x_55 = lean_unsigned_to_nat(0u);
x_39 = x_52;
x_40 = x_53;
x_41 = x_55;
goto block_49;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_66, x_10);
x_68 = lean_nat_add(x_67, x_11);
lean_dec(x_11);
x_69 = lean_nat_add(x_67, x_25);
lean_dec(x_67);
lean_inc_ref(x_5);
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set(x_23, 3, x_5);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 0, x_69);
x_70 = x_23;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_69);
lean_ctor_set(x_84, 1, x_3);
lean_ctor_set(x_84, 2, x_4);
lean_ctor_set(x_84, 3, x_5);
lean_ctor_set(x_84, 4, x_14);
x_70 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_71; uint8_t x_72; uint8_t x_77; 
x_77 = !lean_is_exclusive(x_5);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_5, 4);
lean_dec(x_78);
x_79 = lean_ctor_get(x_5, 3);
lean_dec(x_79);
x_80 = lean_ctor_get(x_5, 2);
lean_dec(x_80);
x_81 = lean_ctor_get(x_5, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_5, 0);
lean_dec(x_82);
x_71 = x_5;
x_72 = x_77;
goto block_76;
}
else
{
lean_dec(x_5);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
lean_ctor_set(x_71, 4, x_15);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 2, x_13);
lean_ctor_set(x_71, 1, x_12);
lean_ctor_set(x_71, 0, x_68);
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_12);
lean_ctor_set(x_75, 2, x_13);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set(x_75, 4, x_15);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_93, x_92);
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
lean_ctor_set(x_95, 2, x_4);
lean_ctor_set(x_95, 3, x_5);
lean_ctor_set(x_95, 4, x_6);
return x_95;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_6, 3);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_121; 
x_97 = lean_ctor_get(x_6, 4);
x_98 = lean_ctor_get(x_6, 1);
x_99 = lean_ctor_get(x_6, 2);
x_121 = !lean_is_exclusive(x_6);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_6, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_6, 0);
lean_dec(x_123);
x_100 = x_6;
x_101 = x_121;
goto block_120;
}
else
{
lean_inc(x_97);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_6);
x_100 = lean_box(0);
x_101 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_116; 
x_102 = lean_ctor_get(x_96, 1);
x_103 = lean_ctor_get(x_96, 2);
x_116 = !lean_is_exclusive(x_96);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_96, 4);
lean_dec(x_117);
x_118 = lean_ctor_get(x_96, 3);
lean_dec(x_118);
x_119 = lean_ctor_get(x_96, 0);
lean_dec(x_119);
x_104 = x_96;
x_105 = x_116;
goto block_115;
}
else
{
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_box(0);
x_105 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(3u);
x_107 = lean_unsigned_to_nat(1u);
lean_inc_n(x_97, 2);
if (x_105 == 0)
{
lean_ctor_set(x_104, 4, x_97);
lean_ctor_set(x_104, 3, x_97);
lean_ctor_set(x_104, 2, x_4);
lean_ctor_set(x_104, 1, x_3);
lean_ctor_set(x_104, 0, x_107);
x_108 = x_104;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_3);
lean_ctor_set(x_114, 2, x_4);
lean_ctor_set(x_114, 3, x_97);
lean_ctor_set(x_114, 4, x_97);
x_108 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_109; 
lean_inc(x_97);
if (x_101 == 0)
{
lean_ctor_set(x_100, 3, x_97);
lean_ctor_set(x_100, 0, x_107);
x_109 = x_100;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_98);
lean_ctor_set(x_112, 2, x_99);
lean_ctor_set(x_112, 3, x_97);
lean_ctor_set(x_112, 4, x_97);
x_109 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_102);
lean_ctor_set(x_110, 2, x_103);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_109);
return x_110;
}
}
}
}
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_6, 4);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_136; 
x_125 = lean_ctor_get(x_6, 1);
x_126 = lean_ctor_get(x_6, 2);
x_136 = !lean_is_exclusive(x_6);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_6, 4);
lean_dec(x_137);
x_138 = lean_ctor_get(x_6, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_6, 0);
lean_dec(x_139);
x_127 = x_6;
x_128 = x_136;
goto block_135;
}
else
{
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_6);
x_127 = lean_box(0);
x_128 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_unsigned_to_nat(3u);
x_130 = lean_unsigned_to_nat(1u);
if (x_128 == 0)
{
lean_ctor_set(x_127, 4, x_96);
lean_ctor_set(x_127, 2, x_4);
lean_ctor_set(x_127, 1, x_3);
lean_ctor_set(x_127, 0, x_130);
x_131 = x_127;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_3);
lean_ctor_set(x_134, 2, x_4);
lean_ctor_set(x_134, 3, x_96);
lean_ctor_set(x_134, 4, x_96);
x_131 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_125);
lean_ctor_set(x_132, 2, x_126);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_124);
return x_132;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_unsigned_to_nat(2u);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_3);
lean_ctor_set(x_141, 2, x_4);
lean_ctor_set(x_141, 3, x_124);
lean_ctor_set(x_141, 4, x_6);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
lean_ctor_set(x_143, 2, x_4);
lean_ctor_set(x_143, 3, x_6);
lean_ctor_set(x_143, 4, x_6);
return x_143;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_mul(x_11, x_5);
x_13 = lean_nat_dec_lt(x_12, x_6);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_14, x_5);
x_16 = lean_nat_add(x_15, x_6);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_81; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_81 = !lean_is_exclusive(x_4);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_4, 4);
lean_dec(x_82);
x_83 = lean_ctor_get(x_4, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_4, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_4, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_4, 0);
lean_dec(x_86);
x_18 = x_4;
x_19 = x_81;
goto block_80;
}
else
{
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
x_24 = lean_ctor_get(x_9, 4);
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_mul(x_26, x_25);
x_28 = lean_nat_dec_lt(x_20, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_55; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_9, 4);
lean_dec(x_56);
x_57 = lean_ctor_get(x_9, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 0);
lean_dec(x_60);
x_29 = x_9;
x_30 = x_55;
goto block_54;
}
else
{
lean_dec(x_9);
x_29 = lean_box(0);
x_30 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_31, x_5);
x_33 = lean_nat_add(x_32, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
x_45 = x_52;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = lean_unsigned_to_nat(0u);
x_45 = x_53;
goto block_51;
}
block_44:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_10);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set(x_29, 2, x_8);
lean_ctor_set(x_29, 1, x_7);
lean_ctor_set(x_29, 0, x_37);
x_38 = x_29;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_7);
lean_ctor_set(x_43, 2, x_8);
lean_ctor_set(x_43, 3, x_24);
lean_ctor_set(x_43, 4, x_10);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_38);
lean_ctor_set(x_18, 3, x_35);
lean_ctor_set(x_18, 2, x_22);
lean_ctor_set(x_18, 1, x_21);
lean_ctor_set(x_18, 0, x_33);
x_39 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_21);
lean_ctor_set(x_41, 2, x_22);
lean_ctor_set(x_41, 3, x_35);
lean_ctor_set(x_41, 4, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_nat_add(x_32, x_45);
lean_dec(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_3);
lean_ctor_set(x_47, 4, x_23);
x_48 = lean_nat_add(x_31, x_25);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_24, 0);
lean_inc(x_49);
x_34 = x_48;
x_35 = x_47;
x_36 = x_49;
goto block_44;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_34 = x_48;
x_35 = x_47;
x_36 = x_50;
goto block_44;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_61, x_5);
x_63 = lean_nat_add(x_62, x_6);
lean_dec(x_6);
x_64 = lean_nat_add(x_62, x_20);
lean_dec(x_62);
lean_inc_ref(x_3);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_9);
lean_ctor_set(x_18, 3, x_3);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 0, x_64);
x_65 = x_18;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_1);
lean_ctor_set(x_79, 2, x_2);
lean_ctor_set(x_79, 3, x_3);
lean_ctor_set(x_79, 4, x_9);
x_65 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_66; uint8_t x_67; uint8_t x_72; 
x_72 = !lean_is_exclusive(x_3);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_3, 4);
lean_dec(x_73);
x_74 = lean_ctor_get(x_3, 3);
lean_dec(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_dec(x_75);
x_76 = lean_ctor_get(x_3, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_3, 0);
lean_dec(x_77);
x_66 = x_3;
x_67 = x_72;
goto block_71;
}
else
{
lean_dec(x_3);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
lean_ctor_set(x_66, 4, x_10);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 2, x_8);
lean_ctor_set(x_66, 1, x_7);
lean_ctor_set(x_66, 0, x_63);
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_7);
lean_ctor_set(x_70, 2, x_8);
lean_ctor_set(x_70, 3, x_65);
lean_ctor_set(x_70, 4, x_10);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_88, x_87);
x_90 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_1);
lean_ctor_set(x_90, 2, x_2);
lean_ctor_set(x_90, 3, x_3);
lean_ctor_set(x_90, 4, x_4);
return x_90;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_4, 3);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 4);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_107; 
x_93 = lean_ctor_get(x_4, 0);
x_94 = lean_ctor_get(x_4, 1);
x_95 = lean_ctor_get(x_4, 2);
x_107 = !lean_is_exclusive(x_4);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_4, 4);
lean_dec(x_108);
x_109 = lean_ctor_get(x_4, 3);
lean_dec(x_109);
x_96 = x_4;
x_97 = x_107;
goto block_106;
}
else
{
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_4);
x_96 = lean_box(0);
x_97 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_91, 0);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_99, x_93);
lean_dec(x_93);
x_101 = lean_nat_add(x_99, x_98);
if (x_97 == 0)
{
lean_ctor_set(x_96, 4, x_91);
lean_ctor_set(x_96, 3, x_3);
lean_ctor_set(x_96, 2, x_2);
lean_ctor_set(x_96, 1, x_1);
lean_ctor_set(x_96, 0, x_101);
x_102 = x_96;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_1);
lean_ctor_set(x_105, 2, x_2);
lean_ctor_set(x_105, 3, x_3);
lean_ctor_set(x_105, 4, x_91);
x_102 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_94);
lean_ctor_set(x_103, 2, x_95);
lean_ctor_set(x_103, 3, x_102);
lean_ctor_set(x_103, 4, x_92);
return x_103;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_133; 
x_110 = lean_ctor_get(x_4, 1);
x_111 = lean_ctor_get(x_4, 2);
x_133 = !lean_is_exclusive(x_4);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_4, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_4, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_4, 0);
lean_dec(x_136);
x_112 = x_4;
x_113 = x_133;
goto block_132;
}
else
{
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_4);
x_112 = lean_box(0);
x_113 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_128; 
x_114 = lean_ctor_get(x_91, 1);
x_115 = lean_ctor_get(x_91, 2);
x_128 = !lean_is_exclusive(x_91);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_91, 4);
lean_dec(x_129);
x_130 = lean_ctor_get(x_91, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_91, 0);
lean_dec(x_131);
x_116 = x_91;
x_117 = x_128;
goto block_127;
}
else
{
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_91);
x_116 = lean_box(0);
x_117 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_unsigned_to_nat(3u);
x_119 = lean_unsigned_to_nat(1u);
if (x_117 == 0)
{
lean_ctor_set(x_116, 4, x_92);
lean_ctor_set(x_116, 3, x_92);
lean_ctor_set(x_116, 2, x_2);
lean_ctor_set(x_116, 1, x_1);
lean_ctor_set(x_116, 0, x_119);
x_120 = x_116;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_1);
lean_ctor_set(x_126, 2, x_2);
lean_ctor_set(x_126, 3, x_92);
lean_ctor_set(x_126, 4, x_92);
x_120 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_121; 
if (x_113 == 0)
{
lean_ctor_set(x_112, 3, x_92);
lean_ctor_set(x_112, 0, x_119);
x_121 = x_112;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_110);
lean_ctor_set(x_124, 2, x_111);
lean_ctor_set(x_124, 3, x_92);
lean_ctor_set(x_124, 4, x_92);
x_121 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_115);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_121);
return x_122;
}
}
}
}
}
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_4, 4);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_149; 
x_138 = lean_ctor_get(x_4, 1);
x_139 = lean_ctor_get(x_4, 2);
x_149 = !lean_is_exclusive(x_4);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_4, 4);
lean_dec(x_150);
x_151 = lean_ctor_get(x_4, 3);
lean_dec(x_151);
x_152 = lean_ctor_get(x_4, 0);
lean_dec(x_152);
x_140 = x_4;
x_141 = x_149;
goto block_148;
}
else
{
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_4);
x_140 = lean_box(0);
x_141 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_unsigned_to_nat(3u);
x_143 = lean_unsigned_to_nat(1u);
if (x_141 == 0)
{
lean_ctor_set(x_140, 4, x_91);
lean_ctor_set(x_140, 2, x_2);
lean_ctor_set(x_140, 1, x_1);
lean_ctor_set(x_140, 0, x_143);
x_144 = x_140;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_1);
lean_ctor_set(x_147, 2, x_2);
lean_ctor_set(x_147, 3, x_91);
lean_ctor_set(x_147, 4, x_91);
x_144 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_138);
lean_ctor_set(x_145, 2, x_139);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set(x_145, 4, x_137);
return x_145;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_164; 
x_153 = lean_ctor_get(x_4, 0);
x_154 = lean_ctor_get(x_4, 1);
x_155 = lean_ctor_get(x_4, 2);
x_164 = !lean_is_exclusive(x_4);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_4, 4);
lean_dec(x_165);
x_166 = lean_ctor_get(x_4, 3);
lean_dec(x_166);
x_156 = x_4;
x_157 = x_164;
goto block_163;
}
else
{
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_4);
x_156 = lean_box(0);
x_157 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_158; 
if (x_157 == 0)
{
lean_ctor_set(x_156, 3, x_137);
x_158 = x_156;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_155);
lean_ctor_set(x_162, 3, x_137);
lean_ctor_set(x_162, 4, x_137);
x_158 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_1);
lean_ctor_set(x_160, 2, x_2);
lean_ctor_set(x_160, 3, x_137);
lean_ctor_set(x_160, 4, x_158);
return x_160;
}
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_1);
lean_ctor_set(x_168, 2, x_2);
lean_ctor_set(x_168, 3, x_4);
lean_ctor_set(x_168, 4, x_4);
return x_168;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_mul(x_16, x_10);
x_18 = lean_nat_dec_lt(x_17, x_11);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_19, x_10);
x_21 = lean_nat_add(x_20, x_11);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_5);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; uint8_t x_86; 
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_6, 4);
lean_dec(x_87);
x_88 = lean_ctor_get(x_6, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_6, 2);
lean_dec(x_89);
x_90 = lean_ctor_get(x_6, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_6, 0);
lean_dec(x_91);
x_23 = x_6;
x_24 = x_86;
goto block_85;
}
else
{
lean_dec(x_6);
x_23 = lean_box(0);
x_24 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_mul(x_31, x_30);
x_33 = lean_nat_dec_lt(x_25, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_60; 
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_60 = !lean_is_exclusive(x_14);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_14, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_14, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_14, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_14, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_14, 0);
lean_dec(x_65);
x_34 = x_14;
x_35 = x_60;
goto block_59;
}
else
{
lean_dec(x_14);
x_34 = lean_box(0);
x_35 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_36, x_10);
x_38 = lean_nat_add(x_37, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_28, 0);
lean_inc(x_57);
x_50 = x_57;
goto block_56;
}
else
{
lean_object* x_58; 
x_58 = lean_unsigned_to_nat(0u);
x_50 = x_58;
goto block_56;
}
block_49:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_nat_add(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
if (x_35 == 0)
{
lean_ctor_set(x_34, 4, x_15);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_13);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 0, x_42);
x_43 = x_34;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_12);
lean_ctor_set(x_48, 2, x_13);
lean_ctor_set(x_48, 3, x_29);
lean_ctor_set(x_48, 4, x_15);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_43);
lean_ctor_set(x_23, 3, x_40);
lean_ctor_set(x_23, 2, x_27);
lean_ctor_set(x_23, 1, x_26);
lean_ctor_set(x_23, 0, x_38);
x_44 = x_23;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_26);
lean_ctor_set(x_46, 2, x_27);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
block_56:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_nat_add(x_37, x_50);
lean_dec(x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 2, x_4);
lean_ctor_set(x_52, 3, x_5);
lean_ctor_set(x_52, 4, x_28);
x_53 = lean_nat_add(x_36, x_30);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
x_39 = x_53;
x_40 = x_52;
x_41 = x_54;
goto block_49;
}
else
{
lean_object* x_55; 
x_55 = lean_unsigned_to_nat(0u);
x_39 = x_53;
x_40 = x_52;
x_41 = x_55;
goto block_49;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_66, x_10);
x_68 = lean_nat_add(x_67, x_11);
lean_dec(x_11);
x_69 = lean_nat_add(x_67, x_25);
lean_dec(x_67);
lean_inc_ref(x_5);
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set(x_23, 3, x_5);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 0, x_69);
x_70 = x_23;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_69);
lean_ctor_set(x_84, 1, x_3);
lean_ctor_set(x_84, 2, x_4);
lean_ctor_set(x_84, 3, x_5);
lean_ctor_set(x_84, 4, x_14);
x_70 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_71; uint8_t x_72; uint8_t x_77; 
x_77 = !lean_is_exclusive(x_5);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_5, 4);
lean_dec(x_78);
x_79 = lean_ctor_get(x_5, 3);
lean_dec(x_79);
x_80 = lean_ctor_get(x_5, 2);
lean_dec(x_80);
x_81 = lean_ctor_get(x_5, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_5, 0);
lean_dec(x_82);
x_71 = x_5;
x_72 = x_77;
goto block_76;
}
else
{
lean_dec(x_5);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
lean_ctor_set(x_71, 4, x_15);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 2, x_13);
lean_ctor_set(x_71, 1, x_12);
lean_ctor_set(x_71, 0, x_68);
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_12);
lean_ctor_set(x_75, 2, x_13);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set(x_75, 4, x_15);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_93, x_92);
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
lean_ctor_set(x_95, 2, x_4);
lean_ctor_set(x_95, 3, x_5);
lean_ctor_set(x_95, 4, x_6);
return x_95;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_6, 3);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_6, 4);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_112; 
x_98 = lean_ctor_get(x_6, 0);
x_99 = lean_ctor_get(x_6, 1);
x_100 = lean_ctor_get(x_6, 2);
x_112 = !lean_is_exclusive(x_6);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_6, 4);
lean_dec(x_113);
x_114 = lean_ctor_get(x_6, 3);
lean_dec(x_114);
x_101 = x_6;
x_102 = x_112;
goto block_111;
}
else
{
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_6);
x_101 = lean_box(0);
x_102 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_96, 0);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_104, x_98);
lean_dec(x_98);
x_106 = lean_nat_add(x_104, x_103);
if (x_102 == 0)
{
lean_ctor_set(x_101, 4, x_96);
lean_ctor_set(x_101, 3, x_5);
lean_ctor_set(x_101, 2, x_4);
lean_ctor_set(x_101, 1, x_3);
lean_ctor_set(x_101, 0, x_106);
x_107 = x_101;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_4);
lean_ctor_set(x_110, 3, x_5);
lean_ctor_set(x_110, 4, x_96);
x_107 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_99);
lean_ctor_set(x_108, 2, x_100);
lean_ctor_set(x_108, 3, x_107);
lean_ctor_set(x_108, 4, x_97);
return x_108;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_138; 
x_115 = lean_ctor_get(x_6, 1);
x_116 = lean_ctor_get(x_6, 2);
x_138 = !lean_is_exclusive(x_6);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_6, 4);
lean_dec(x_139);
x_140 = lean_ctor_get(x_6, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_6, 0);
lean_dec(x_141);
x_117 = x_6;
x_118 = x_138;
goto block_137;
}
else
{
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_6);
x_117 = lean_box(0);
x_118 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_133; 
x_119 = lean_ctor_get(x_96, 1);
x_120 = lean_ctor_get(x_96, 2);
x_133 = !lean_is_exclusive(x_96);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_96, 4);
lean_dec(x_134);
x_135 = lean_ctor_get(x_96, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_96, 0);
lean_dec(x_136);
x_121 = x_96;
x_122 = x_133;
goto block_132;
}
else
{
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_96);
x_121 = lean_box(0);
x_122 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_unsigned_to_nat(1u);
if (x_122 == 0)
{
lean_ctor_set(x_121, 4, x_97);
lean_ctor_set(x_121, 3, x_97);
lean_ctor_set(x_121, 2, x_4);
lean_ctor_set(x_121, 1, x_3);
lean_ctor_set(x_121, 0, x_124);
x_125 = x_121;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_124);
lean_ctor_set(x_131, 1, x_3);
lean_ctor_set(x_131, 2, x_4);
lean_ctor_set(x_131, 3, x_97);
lean_ctor_set(x_131, 4, x_97);
x_125 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_126; 
if (x_118 == 0)
{
lean_ctor_set(x_117, 3, x_97);
lean_ctor_set(x_117, 0, x_124);
x_126 = x_117;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_115);
lean_ctor_set(x_129, 2, x_116);
lean_ctor_set(x_129, 3, x_97);
lean_ctor_set(x_129, 4, x_97);
x_126 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_125);
lean_ctor_set(x_127, 4, x_126);
return x_127;
}
}
}
}
}
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_6, 4);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_154; 
x_143 = lean_ctor_get(x_6, 1);
x_144 = lean_ctor_get(x_6, 2);
x_154 = !lean_is_exclusive(x_6);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_6, 4);
lean_dec(x_155);
x_156 = lean_ctor_get(x_6, 3);
lean_dec(x_156);
x_157 = lean_ctor_get(x_6, 0);
lean_dec(x_157);
x_145 = x_6;
x_146 = x_154;
goto block_153;
}
else
{
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_6);
x_145 = lean_box(0);
x_146 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_unsigned_to_nat(3u);
x_148 = lean_unsigned_to_nat(1u);
if (x_146 == 0)
{
lean_ctor_set(x_145, 4, x_96);
lean_ctor_set(x_145, 2, x_4);
lean_ctor_set(x_145, 1, x_3);
lean_ctor_set(x_145, 0, x_148);
x_149 = x_145;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_3);
lean_ctor_set(x_152, 2, x_4);
lean_ctor_set(x_152, 3, x_96);
lean_ctor_set(x_152, 4, x_96);
x_149 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_143);
lean_ctor_set(x_150, 2, x_144);
lean_ctor_set(x_150, 3, x_149);
lean_ctor_set(x_150, 4, x_142);
return x_150;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_169; 
x_158 = lean_ctor_get(x_6, 0);
x_159 = lean_ctor_get(x_6, 1);
x_160 = lean_ctor_get(x_6, 2);
x_169 = !lean_is_exclusive(x_6);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_6, 4);
lean_dec(x_170);
x_171 = lean_ctor_get(x_6, 3);
lean_dec(x_171);
x_161 = x_6;
x_162 = x_169;
goto block_168;
}
else
{
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_6);
x_161 = lean_box(0);
x_162 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_163; 
if (x_162 == 0)
{
lean_ctor_set(x_161, 3, x_142);
x_163 = x_161;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_159);
lean_ctor_set(x_167, 2, x_160);
lean_ctor_set(x_167, 3, x_142);
lean_ctor_set(x_167, 4, x_142);
x_163 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_unsigned_to_nat(2u);
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_3);
lean_ctor_set(x_165, 2, x_4);
lean_ctor_set(x_165, 3, x_142);
lean_ctor_set(x_165, 4, x_163);
return x_165;
}
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_3);
lean_ctor_set(x_173, 2, x_4);
lean_ctor_set(x_173, 3, x_6);
lean_ctor_set(x_173, 4, x_6);
return x_173;
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_unsigned_to_nat(276u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(277u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_mul(x_11, x_5);
x_13 = lean_nat_dec_lt(x_12, x_6);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_14, x_5);
x_16 = lean_nat_add(x_15, x_6);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_87; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_87 = !lean_is_exclusive(x_4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_4, 4);
lean_dec(x_88);
x_89 = lean_ctor_get(x_4, 3);
lean_dec(x_89);
x_90 = lean_ctor_get(x_4, 2);
lean_dec(x_90);
x_91 = lean_ctor_get(x_4, 1);
lean_dec(x_91);
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_18 = x_4;
x_19 = x_87;
goto block_86;
}
else
{
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_87;
goto block_86;
}
block_86:
{
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
x_24 = lean_ctor_get(x_9, 4);
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_mul(x_26, x_25);
x_28 = lean_nat_dec_lt(x_20, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_55; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_9, 4);
lean_dec(x_56);
x_57 = lean_ctor_get(x_9, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 0);
lean_dec(x_60);
x_29 = x_9;
x_30 = x_55;
goto block_54;
}
else
{
lean_dec(x_9);
x_29 = lean_box(0);
x_30 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_31, x_5);
x_33 = lean_nat_add(x_32, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
x_45 = x_52;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = lean_unsigned_to_nat(0u);
x_45 = x_53;
goto block_51;
}
block_44:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_10);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set(x_29, 2, x_8);
lean_ctor_set(x_29, 1, x_7);
lean_ctor_set(x_29, 0, x_37);
x_38 = x_29;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_7);
lean_ctor_set(x_43, 2, x_8);
lean_ctor_set(x_43, 3, x_24);
lean_ctor_set(x_43, 4, x_10);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_38);
lean_ctor_set(x_18, 3, x_34);
lean_ctor_set(x_18, 2, x_22);
lean_ctor_set(x_18, 1, x_21);
lean_ctor_set(x_18, 0, x_33);
x_39 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_21);
lean_ctor_set(x_41, 2, x_22);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_nat_add(x_32, x_45);
lean_dec(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_3);
lean_ctor_set(x_47, 4, x_23);
x_48 = lean_nat_add(x_31, x_25);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_24, 0);
lean_inc(x_49);
x_34 = x_47;
x_35 = x_48;
x_36 = x_49;
goto block_44;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_34 = x_47;
x_35 = x_48;
x_36 = x_50;
goto block_44;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_61, x_5);
x_63 = lean_nat_add(x_62, x_6);
lean_dec(x_6);
x_64 = lean_nat_add(x_62, x_20);
lean_dec(x_62);
lean_inc_ref(x_3);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_9);
lean_ctor_set(x_18, 3, x_3);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 0, x_64);
x_65 = x_18;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_1);
lean_ctor_set(x_79, 2, x_2);
lean_ctor_set(x_79, 3, x_3);
lean_ctor_set(x_79, 4, x_9);
x_65 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_66; uint8_t x_67; uint8_t x_72; 
x_72 = !lean_is_exclusive(x_3);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_3, 4);
lean_dec(x_73);
x_74 = lean_ctor_get(x_3, 3);
lean_dec(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_dec(x_75);
x_76 = lean_ctor_get(x_3, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_3, 0);
lean_dec(x_77);
x_66 = x_3;
x_67 = x_72;
goto block_71;
}
else
{
lean_dec(x_3);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
lean_ctor_set(x_66, 4, x_10);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 2, x_8);
lean_ctor_set(x_66, 1, x_7);
lean_ctor_set(x_66, 0, x_63);
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_7);
lean_ctor_set(x_70, 2, x_8);
lean_ctor_set(x_70, 3, x_65);
lean_ctor_set(x_70, 4, x_10);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_9);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(1);
x_81 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
x_82 = l_panic___redArg(x_80, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_del_object(x_18);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_box(1);
x_84 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
x_85 = l_panic___redArg(x_83, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_3, 0);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_94, x_93);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_1);
lean_ctor_set(x_96, 2, x_2);
lean_ctor_set(x_96, 3, x_3);
lean_ctor_set(x_96, 4, x_4);
return x_96;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_4, 3);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_4, 4);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_113; 
x_99 = lean_ctor_get(x_4, 0);
x_100 = lean_ctor_get(x_4, 1);
x_101 = lean_ctor_get(x_4, 2);
x_113 = !lean_is_exclusive(x_4);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_4, 4);
lean_dec(x_114);
x_115 = lean_ctor_get(x_4, 3);
lean_dec(x_115);
x_102 = x_4;
x_103 = x_113;
goto block_112;
}
else
{
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_4);
x_102 = lean_box(0);
x_103 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_97, 0);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_105, x_99);
lean_dec(x_99);
x_107 = lean_nat_add(x_105, x_104);
if (x_103 == 0)
{
lean_ctor_set(x_102, 4, x_97);
lean_ctor_set(x_102, 3, x_3);
lean_ctor_set(x_102, 2, x_2);
lean_ctor_set(x_102, 1, x_1);
lean_ctor_set(x_102, 0, x_107);
x_108 = x_102;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_1);
lean_ctor_set(x_111, 2, x_2);
lean_ctor_set(x_111, 3, x_3);
lean_ctor_set(x_111, 4, x_97);
x_108 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_101);
lean_ctor_set(x_109, 3, x_108);
lean_ctor_set(x_109, 4, x_98);
return x_109;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_139; 
x_116 = lean_ctor_get(x_4, 1);
x_117 = lean_ctor_get(x_4, 2);
x_139 = !lean_is_exclusive(x_4);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_4, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_4, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_4, 0);
lean_dec(x_142);
x_118 = x_4;
x_119 = x_139;
goto block_138;
}
else
{
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_4);
x_118 = lean_box(0);
x_119 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_134; 
x_120 = lean_ctor_get(x_97, 1);
x_121 = lean_ctor_get(x_97, 2);
x_134 = !lean_is_exclusive(x_97);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_97, 4);
lean_dec(x_135);
x_136 = lean_ctor_get(x_97, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_97, 0);
lean_dec(x_137);
x_122 = x_97;
x_123 = x_134;
goto block_133;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_97);
x_122 = lean_box(0);
x_123 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_unsigned_to_nat(1u);
if (x_123 == 0)
{
lean_ctor_set(x_122, 4, x_98);
lean_ctor_set(x_122, 3, x_98);
lean_ctor_set(x_122, 2, x_2);
lean_ctor_set(x_122, 1, x_1);
lean_ctor_set(x_122, 0, x_125);
x_126 = x_122;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_1);
lean_ctor_set(x_132, 2, x_2);
lean_ctor_set(x_132, 3, x_98);
lean_ctor_set(x_132, 4, x_98);
x_126 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_127; 
if (x_119 == 0)
{
lean_ctor_set(x_118, 3, x_98);
lean_ctor_set(x_118, 0, x_125);
x_127 = x_118;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_116);
lean_ctor_set(x_130, 2, x_117);
lean_ctor_set(x_130, 3, x_98);
lean_ctor_set(x_130, 4, x_98);
x_127 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_120);
lean_ctor_set(x_128, 2, x_121);
lean_ctor_set(x_128, 3, x_126);
lean_ctor_set(x_128, 4, x_127);
return x_128;
}
}
}
}
}
}
else
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_4, 4);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_155; 
x_144 = lean_ctor_get(x_4, 1);
x_145 = lean_ctor_get(x_4, 2);
x_155 = !lean_is_exclusive(x_4);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_4, 4);
lean_dec(x_156);
x_157 = lean_ctor_get(x_4, 3);
lean_dec(x_157);
x_158 = lean_ctor_get(x_4, 0);
lean_dec(x_158);
x_146 = x_4;
x_147 = x_155;
goto block_154;
}
else
{
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_4);
x_146 = lean_box(0);
x_147 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_unsigned_to_nat(1u);
if (x_147 == 0)
{
lean_ctor_set(x_146, 4, x_97);
lean_ctor_set(x_146, 2, x_2);
lean_ctor_set(x_146, 1, x_1);
lean_ctor_set(x_146, 0, x_149);
x_150 = x_146;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_1);
lean_ctor_set(x_153, 2, x_2);
lean_ctor_set(x_153, 3, x_97);
lean_ctor_set(x_153, 4, x_97);
x_150 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_151, 2, x_145);
lean_ctor_set(x_151, 3, x_150);
lean_ctor_set(x_151, 4, x_143);
return x_151;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_1);
lean_ctor_set(x_160, 2, x_2);
lean_ctor_set(x_160, 3, x_143);
lean_ctor_set(x_160, 4, x_4);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_1);
lean_ctor_set(x_162, 2, x_2);
lean_ctor_set(x_162, 3, x_4);
lean_ctor_set(x_162, 4, x_4);
return x_162;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 4);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_mul(x_13, x_7);
x_15 = lean_nat_dec_lt(x_14, x_8);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_16, x_7);
x_18 = lean_nat_add(x_17, x_8);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_5);
lean_ctor_set(x_19, 4, x_6);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_89; 
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_6, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_6, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_6, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_6, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_6, 0);
lean_dec(x_94);
x_20 = x_6;
x_21 = x_89;
goto block_88;
}
else
{
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
x_24 = lean_ctor_get(x_11, 2);
x_25 = lean_ctor_get(x_11, 3);
x_26 = lean_ctor_get(x_11, 4);
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_mul(x_28, x_27);
x_30 = lean_nat_dec_lt(x_22, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_57; 
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_11, 4);
lean_dec(x_58);
x_59 = lean_ctor_get(x_11, 3);
lean_dec(x_59);
x_60 = lean_ctor_get(x_11, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_11, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_11, 0);
lean_dec(x_62);
x_31 = x_11;
x_32 = x_57;
goto block_56;
}
else
{
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_47; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_33, x_7);
x_35 = lean_nat_add(x_34, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_25, 0);
lean_inc(x_54);
x_47 = x_54;
goto block_53;
}
else
{
lean_object* x_55; 
x_55 = lean_unsigned_to_nat(0u);
x_47 = x_55;
goto block_53;
}
block_46:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_nat_add(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_32 == 0)
{
lean_ctor_set(x_31, 4, x_12);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 2, x_10);
lean_ctor_set(x_31, 1, x_9);
lean_ctor_set(x_31, 0, x_39);
x_40 = x_31;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_9);
lean_ctor_set(x_45, 2, x_10);
lean_ctor_set(x_45, 3, x_26);
lean_ctor_set(x_45, 4, x_12);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 4, x_40);
lean_ctor_set(x_20, 3, x_36);
lean_ctor_set(x_20, 2, x_24);
lean_ctor_set(x_20, 1, x_23);
lean_ctor_set(x_20, 0, x_35);
x_41 = x_20;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_43, 2, x_24);
lean_ctor_set(x_43, 3, x_36);
lean_ctor_set(x_43, 4, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_nat_add(x_34, x_47);
lean_dec(x_47);
lean_dec(x_34);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set(x_49, 3, x_5);
lean_ctor_set(x_49, 4, x_25);
x_50 = lean_nat_add(x_33, x_27);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_26, 0);
lean_inc(x_51);
x_36 = x_49;
x_37 = x_50;
x_38 = x_51;
goto block_46;
}
else
{
lean_object* x_52; 
x_52 = lean_unsigned_to_nat(0u);
x_36 = x_49;
x_37 = x_50;
x_38 = x_52;
goto block_46;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_63, x_7);
x_65 = lean_nat_add(x_64, x_8);
lean_dec(x_8);
x_66 = lean_nat_add(x_64, x_22);
lean_dec(x_64);
lean_inc_ref(x_5);
if (x_21 == 0)
{
lean_ctor_set(x_20, 4, x_11);
lean_ctor_set(x_20, 3, x_5);
lean_ctor_set(x_20, 2, x_4);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 0, x_66);
x_67 = x_20;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_3);
lean_ctor_set(x_81, 2, x_4);
lean_ctor_set(x_81, 3, x_5);
lean_ctor_set(x_81, 4, x_11);
x_67 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_68; uint8_t x_69; uint8_t x_74; 
x_74 = !lean_is_exclusive(x_5);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_5, 4);
lean_dec(x_75);
x_76 = lean_ctor_get(x_5, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_5, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_5, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_5, 0);
lean_dec(x_79);
x_68 = x_5;
x_69 = x_74;
goto block_73;
}
else
{
lean_dec(x_5);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
lean_ctor_set(x_68, 4, x_12);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set(x_68, 2, x_10);
lean_ctor_set(x_68, 1, x_9);
lean_ctor_set(x_68, 0, x_65);
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_9);
lean_ctor_set(x_72, 2, x_10);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set(x_72, 4, x_12);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_11);
lean_del_object(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_box(1);
x_83 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
x_84 = l_panic___redArg(x_82, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_del_object(x_20);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = lean_box(1);
x_86 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
x_87 = l_panic___redArg(x_85, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_5, 0);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_96, x_95);
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_3);
lean_ctor_set(x_98, 2, x_4);
lean_ctor_set(x_98, 3, x_5);
lean_ctor_set(x_98, 4, x_6);
return x_98;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_6, 3);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_6, 4);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_115; 
x_101 = lean_ctor_get(x_6, 0);
x_102 = lean_ctor_get(x_6, 1);
x_103 = lean_ctor_get(x_6, 2);
x_115 = !lean_is_exclusive(x_6);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_6, 4);
lean_dec(x_116);
x_117 = lean_ctor_get(x_6, 3);
lean_dec(x_117);
x_104 = x_6;
x_105 = x_115;
goto block_114;
}
else
{
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_6);
x_104 = lean_box(0);
x_105 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_99, 0);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_107, x_101);
lean_dec(x_101);
x_109 = lean_nat_add(x_107, x_106);
if (x_105 == 0)
{
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_104, 3, x_5);
lean_ctor_set(x_104, 2, x_4);
lean_ctor_set(x_104, 1, x_3);
lean_ctor_set(x_104, 0, x_109);
x_110 = x_104;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_3);
lean_ctor_set(x_113, 2, x_4);
lean_ctor_set(x_113, 3, x_5);
lean_ctor_set(x_113, 4, x_99);
x_110 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_102);
lean_ctor_set(x_111, 2, x_103);
lean_ctor_set(x_111, 3, x_110);
lean_ctor_set(x_111, 4, x_100);
return x_111;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_141; 
x_118 = lean_ctor_get(x_6, 1);
x_119 = lean_ctor_get(x_6, 2);
x_141 = !lean_is_exclusive(x_6);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_6, 4);
lean_dec(x_142);
x_143 = lean_ctor_get(x_6, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_6, 0);
lean_dec(x_144);
x_120 = x_6;
x_121 = x_141;
goto block_140;
}
else
{
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_6);
x_120 = lean_box(0);
x_121 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_136; 
x_122 = lean_ctor_get(x_99, 1);
x_123 = lean_ctor_get(x_99, 2);
x_136 = !lean_is_exclusive(x_99);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_99, 4);
lean_dec(x_137);
x_138 = lean_ctor_get(x_99, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_99, 0);
lean_dec(x_139);
x_124 = x_99;
x_125 = x_136;
goto block_135;
}
else
{
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_99);
x_124 = lean_box(0);
x_125 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_unsigned_to_nat(3u);
x_127 = lean_unsigned_to_nat(1u);
if (x_125 == 0)
{
lean_ctor_set(x_124, 4, x_100);
lean_ctor_set(x_124, 3, x_100);
lean_ctor_set(x_124, 2, x_4);
lean_ctor_set(x_124, 1, x_3);
lean_ctor_set(x_124, 0, x_127);
x_128 = x_124;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_3);
lean_ctor_set(x_134, 2, x_4);
lean_ctor_set(x_134, 3, x_100);
lean_ctor_set(x_134, 4, x_100);
x_128 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_129; 
if (x_121 == 0)
{
lean_ctor_set(x_120, 3, x_100);
lean_ctor_set(x_120, 0, x_127);
x_129 = x_120;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_118);
lean_ctor_set(x_132, 2, x_119);
lean_ctor_set(x_132, 3, x_100);
lean_ctor_set(x_132, 4, x_100);
x_129 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_122);
lean_ctor_set(x_130, 2, x_123);
lean_ctor_set(x_130, 3, x_128);
lean_ctor_set(x_130, 4, x_129);
return x_130;
}
}
}
}
}
}
else
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_6, 4);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_157; 
x_146 = lean_ctor_get(x_6, 1);
x_147 = lean_ctor_get(x_6, 2);
x_157 = !lean_is_exclusive(x_6);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_6, 4);
lean_dec(x_158);
x_159 = lean_ctor_get(x_6, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_6, 0);
lean_dec(x_160);
x_148 = x_6;
x_149 = x_157;
goto block_156;
}
else
{
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_6);
x_148 = lean_box(0);
x_149 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_unsigned_to_nat(3u);
x_151 = lean_unsigned_to_nat(1u);
if (x_149 == 0)
{
lean_ctor_set(x_148, 4, x_99);
lean_ctor_set(x_148, 2, x_4);
lean_ctor_set(x_148, 1, x_3);
lean_ctor_set(x_148, 0, x_151);
x_152 = x_148;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_3);
lean_ctor_set(x_155, 2, x_4);
lean_ctor_set(x_155, 3, x_99);
lean_ctor_set(x_155, 4, x_99);
x_152 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_146);
lean_ctor_set(x_153, 2, x_147);
lean_ctor_set(x_153, 3, x_152);
lean_ctor_set(x_153, 4, x_145);
return x_153;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_unsigned_to_nat(2u);
x_162 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_3);
lean_ctor_set(x_162, 2, x_4);
lean_ctor_set(x_162, 3, x_145);
lean_ctor_set(x_162, 4, x_6);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_3);
lean_ctor_set(x_164, 2, x_4);
lean_ctor_set(x_164, 3, x_6);
lean_ctor_set(x_164, 4, x_6);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_mul(x_15, x_5);
x_17 = lean_nat_dec_lt(x_16, x_10);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
x_18 = lean_nat_mul(x_15, x_10);
x_19 = lean_nat_dec_lt(x_18, x_5);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_20, x_5);
x_22 = lean_nat_add(x_21, x_10);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 2, x_2);
lean_ctor_set(x_23, 3, x_3);
lean_ctor_set(x_23, 4, x_4);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_89; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_3, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_3, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_3, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_3, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_3, 0);
lean_dec(x_94);
x_24 = x_3;
x_25 = x_89;
goto block_88;
}
else
{
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 2);
x_30 = lean_ctor_get(x_9, 3);
x_31 = lean_ctor_get(x_9, 4);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_26);
x_34 = lean_nat_dec_lt(x_27, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; uint8_t x_73; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_73 = !lean_is_exclusive(x_9);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_9, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_9, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_9, 2);
lean_dec(x_76);
x_77 = lean_ctor_get(x_9, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_9, 0);
lean_dec(x_78);
x_35 = x_9;
x_36 = x_73;
goto block_72;
}
else
{
lean_dec(x_9);
x_35 = lean_box(0);
x_36 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_60; lean_object* x_61; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_37, x_5);
lean_dec(x_5);
x_39 = lean_nat_add(x_38, x_10);
lean_dec(x_38);
x_60 = lean_nat_add(x_37, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_30, 0);
lean_inc(x_70);
x_61 = x_70;
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = lean_unsigned_to_nat(0u);
x_61 = x_71;
goto block_69;
}
block_59:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_inc_ref(x_4);
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_4);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 2, x_2);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set(x_35, 0, x_43);
x_44 = x_35;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_2);
lean_ctor_set(x_58, 3, x_31);
lean_ctor_set(x_58, 4, x_4);
x_44 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_45; uint8_t x_46; uint8_t x_51; 
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_4, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_4, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_4, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_4, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_4, 0);
lean_dec(x_56);
x_45 = x_4;
x_46 = x_51;
goto block_50;
}
else
{
lean_dec(x_4);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 2, x_29);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 0, x_39);
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_28);
lean_ctor_set(x_49, 2, x_29);
lean_ctor_set(x_49, 3, x_40);
lean_ctor_set(x_49, 4, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
block_69:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_nat_add(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_30);
lean_ctor_set(x_24, 0, x_62);
x_63 = x_24;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_6);
lean_ctor_set(x_68, 2, x_7);
lean_ctor_set(x_68, 3, x_8);
lean_ctor_set(x_68, 4, x_30);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
x_64 = lean_nat_add(x_37, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
x_40 = x_63;
x_41 = x_64;
x_42 = x_65;
goto block_59;
}
else
{
lean_object* x_66; 
x_66 = lean_unsigned_to_nat(0u);
x_40 = x_63;
x_41 = x_64;
x_42 = x_66;
goto block_59;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_79, x_5);
lean_dec(x_5);
x_81 = lean_nat_add(x_80, x_10);
lean_dec(x_80);
x_82 = lean_nat_add(x_79, x_10);
x_83 = lean_nat_add(x_82, x_27);
lean_dec(x_82);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_4);
lean_ctor_set(x_24, 3, x_9);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 0, x_83);
x_84 = x_24;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_1);
lean_ctor_set(x_87, 2, x_2);
lean_ctor_set(x_87, 3, x_9);
lean_ctor_set(x_87, 4, x_4);
x_84 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_6);
lean_ctor_set(x_85, 2, x_7);
lean_ctor_set(x_85, 3, x_8);
lean_ctor_set(x_85, 4, x_84);
return x_85;
}
}
}
}
}
else
{
lean_object* x_95; uint8_t x_96; uint8_t x_158; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_158 = !lean_is_exclusive(x_4);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_4, 4);
lean_dec(x_159);
x_160 = lean_ctor_get(x_4, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_4, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_4, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_4, 0);
lean_dec(x_163);
x_95 = x_4;
x_96 = x_158;
goto block_157;
}
else
{
lean_dec(x_4);
x_95 = lean_box(0);
x_96 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_97 = lean_ctor_get(x_13, 0);
x_98 = lean_ctor_get(x_13, 1);
x_99 = lean_ctor_get(x_13, 2);
x_100 = lean_ctor_get(x_13, 3);
x_101 = lean_ctor_get(x_13, 4);
x_102 = lean_ctor_get(x_14, 0);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_mul(x_103, x_102);
x_105 = lean_nat_dec_lt(x_97, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; uint8_t x_132; 
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_132 = !lean_is_exclusive(x_13);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_13, 4);
lean_dec(x_133);
x_134 = lean_ctor_get(x_13, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_13, 2);
lean_dec(x_135);
x_136 = lean_ctor_get(x_13, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_13, 0);
lean_dec(x_137);
x_106 = x_13;
x_107 = x_132;
goto block_131;
}
else
{
lean_dec(x_13);
x_106 = lean_box(0);
x_107 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_122; 
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_nat_add(x_108, x_5);
x_110 = lean_nat_add(x_109, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_100, 0);
lean_inc(x_129);
x_122 = x_129;
goto block_128;
}
else
{
lean_object* x_130; 
x_130 = lean_unsigned_to_nat(0u);
x_122 = x_130;
goto block_128;
}
block_121:
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_nat_add(x_112, x_113);
lean_dec(x_113);
lean_dec(x_112);
if (x_107 == 0)
{
lean_ctor_set(x_106, 4, x_14);
lean_ctor_set(x_106, 3, x_101);
lean_ctor_set(x_106, 2, x_12);
lean_ctor_set(x_106, 1, x_11);
lean_ctor_set(x_106, 0, x_114);
x_115 = x_106;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_11);
lean_ctor_set(x_120, 2, x_12);
lean_ctor_set(x_120, 3, x_101);
lean_ctor_set(x_120, 4, x_14);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_96 == 0)
{
lean_ctor_set(x_95, 4, x_115);
lean_ctor_set(x_95, 3, x_111);
lean_ctor_set(x_95, 2, x_99);
lean_ctor_set(x_95, 1, x_98);
lean_ctor_set(x_95, 0, x_110);
x_116 = x_95;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_98);
lean_ctor_set(x_118, 2, x_99);
lean_ctor_set(x_118, 3, x_111);
lean_ctor_set(x_118, 4, x_115);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
block_128:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_nat_add(x_109, x_122);
lean_dec(x_122);
lean_dec(x_109);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_1);
lean_ctor_set(x_124, 2, x_2);
lean_ctor_set(x_124, 3, x_3);
lean_ctor_set(x_124, 4, x_100);
x_125 = lean_nat_add(x_108, x_102);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_101, 0);
lean_inc(x_126);
x_111 = x_124;
x_112 = x_125;
x_113 = x_126;
goto block_121;
}
else
{
lean_object* x_127; 
x_127 = lean_unsigned_to_nat(0u);
x_111 = x_124;
x_112 = x_125;
x_113 = x_127;
goto block_121;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_add(x_138, x_5);
x_140 = lean_nat_add(x_139, x_10);
lean_dec(x_10);
x_141 = lean_nat_add(x_139, x_97);
lean_dec(x_139);
lean_inc_ref(x_3);
if (x_96 == 0)
{
lean_ctor_set(x_95, 4, x_13);
lean_ctor_set(x_95, 3, x_3);
lean_ctor_set(x_95, 2, x_2);
lean_ctor_set(x_95, 1, x_1);
lean_ctor_set(x_95, 0, x_141);
x_142 = x_95;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_141);
lean_ctor_set(x_156, 1, x_1);
lean_ctor_set(x_156, 2, x_2);
lean_ctor_set(x_156, 3, x_3);
lean_ctor_set(x_156, 4, x_13);
x_142 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_143; uint8_t x_144; uint8_t x_149; 
x_149 = !lean_is_exclusive(x_3);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_3, 4);
lean_dec(x_150);
x_151 = lean_ctor_get(x_3, 3);
lean_dec(x_151);
x_152 = lean_ctor_get(x_3, 2);
lean_dec(x_152);
x_153 = lean_ctor_get(x_3, 1);
lean_dec(x_153);
x_154 = lean_ctor_get(x_3, 0);
lean_dec(x_154);
x_143 = x_3;
x_144 = x_149;
goto block_148;
}
else
{
lean_dec(x_3);
x_143 = lean_box(0);
x_144 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_145; 
if (x_144 == 0)
{
lean_ctor_set(x_143, 4, x_14);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set(x_143, 2, x_12);
lean_ctor_set(x_143, 1, x_11);
lean_ctor_set(x_143, 0, x_140);
x_145 = x_143;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_11);
lean_ctor_set(x_147, 2, x_12);
lean_ctor_set(x_147, 3, x_142);
lean_ctor_set(x_147, 4, x_14);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
}
}
else
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_3, 4);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_191; 
x_166 = lean_ctor_get(x_3, 0);
x_167 = lean_ctor_get(x_3, 1);
x_168 = lean_ctor_get(x_3, 2);
x_191 = !lean_is_exclusive(x_3);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_3, 4);
lean_dec(x_192);
x_193 = lean_ctor_get(x_3, 3);
lean_dec(x_193);
x_169 = x_3;
x_170 = x_191;
goto block_190;
}
else
{
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_3);
x_169 = lean_box(0);
x_170 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_165, 0);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_add(x_172, x_166);
lean_dec(x_166);
x_174 = lean_nat_add(x_172, x_171);
lean_inc_ref(x_165);
if (x_170 == 0)
{
lean_ctor_set(x_169, 4, x_4);
lean_ctor_set(x_169, 3, x_165);
lean_ctor_set(x_169, 2, x_2);
lean_ctor_set(x_169, 1, x_1);
lean_ctor_set(x_169, 0, x_174);
x_175 = x_169;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_174);
lean_ctor_set(x_189, 1, x_1);
lean_ctor_set(x_189, 2, x_2);
lean_ctor_set(x_189, 3, x_165);
lean_ctor_set(x_189, 4, x_4);
x_175 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_176; uint8_t x_177; uint8_t x_182; 
x_182 = !lean_is_exclusive(x_165);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_165, 4);
lean_dec(x_183);
x_184 = lean_ctor_get(x_165, 3);
lean_dec(x_184);
x_185 = lean_ctor_get(x_165, 2);
lean_dec(x_185);
x_186 = lean_ctor_get(x_165, 1);
lean_dec(x_186);
x_187 = lean_ctor_get(x_165, 0);
lean_dec(x_187);
x_176 = x_165;
x_177 = x_182;
goto block_181;
}
else
{
lean_dec(x_165);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
lean_ctor_set(x_176, 4, x_175);
lean_ctor_set(x_176, 3, x_164);
lean_ctor_set(x_176, 2, x_168);
lean_ctor_set(x_176, 1, x_167);
lean_ctor_set(x_176, 0, x_173);
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_167);
lean_ctor_set(x_180, 2, x_168);
lean_ctor_set(x_180, 3, x_164);
lean_ctor_set(x_180, 4, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_205; 
x_194 = lean_ctor_get(x_3, 1);
x_195 = lean_ctor_get(x_3, 2);
x_205 = !lean_is_exclusive(x_3);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_3, 4);
lean_dec(x_206);
x_207 = lean_ctor_get(x_3, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_3, 0);
lean_dec(x_208);
x_196 = x_3;
x_197 = x_205;
goto block_204;
}
else
{
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_3);
x_196 = lean_box(0);
x_197 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_unsigned_to_nat(3u);
x_199 = lean_unsigned_to_nat(1u);
if (x_197 == 0)
{
lean_ctor_set(x_196, 3, x_165);
lean_ctor_set(x_196, 2, x_2);
lean_ctor_set(x_196, 1, x_1);
lean_ctor_set(x_196, 0, x_199);
x_200 = x_196;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_199);
lean_ctor_set(x_203, 1, x_1);
lean_ctor_set(x_203, 2, x_2);
lean_ctor_set(x_203, 3, x_165);
lean_ctor_set(x_203, 4, x_165);
x_200 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_194);
lean_ctor_set(x_201, 2, x_195);
lean_ctor_set(x_201, 3, x_164);
lean_ctor_set(x_201, 4, x_200);
return x_201;
}
}
}
}
else
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_3, 4);
lean_inc(x_209);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_233; 
lean_inc(x_164);
x_210 = lean_ctor_get(x_3, 1);
x_211 = lean_ctor_get(x_3, 2);
x_233 = !lean_is_exclusive(x_3);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_3, 4);
lean_dec(x_234);
x_235 = lean_ctor_get(x_3, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_3, 0);
lean_dec(x_236);
x_212 = x_3;
x_213 = x_233;
goto block_232;
}
else
{
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_3);
x_212 = lean_box(0);
x_213 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_228; 
x_214 = lean_ctor_get(x_209, 1);
x_215 = lean_ctor_get(x_209, 2);
x_228 = !lean_is_exclusive(x_209);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_209, 4);
lean_dec(x_229);
x_230 = lean_ctor_get(x_209, 3);
lean_dec(x_230);
x_231 = lean_ctor_get(x_209, 0);
lean_dec(x_231);
x_216 = x_209;
x_217 = x_228;
goto block_227;
}
else
{
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_209);
x_216 = lean_box(0);
x_217 = x_228;
goto block_227;
}
block_227:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_unsigned_to_nat(3u);
x_219 = lean_unsigned_to_nat(1u);
if (x_217 == 0)
{
lean_ctor_set(x_216, 4, x_164);
lean_ctor_set(x_216, 3, x_164);
lean_ctor_set(x_216, 2, x_211);
lean_ctor_set(x_216, 1, x_210);
lean_ctor_set(x_216, 0, x_219);
x_220 = x_216;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_226, 0, x_219);
lean_ctor_set(x_226, 1, x_210);
lean_ctor_set(x_226, 2, x_211);
lean_ctor_set(x_226, 3, x_164);
lean_ctor_set(x_226, 4, x_164);
x_220 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_221; 
if (x_213 == 0)
{
lean_ctor_set(x_212, 4, x_164);
lean_ctor_set(x_212, 2, x_2);
lean_ctor_set(x_212, 1, x_1);
lean_ctor_set(x_212, 0, x_219);
x_221 = x_212;
goto block_223;
}
else
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_224, 0, x_219);
lean_ctor_set(x_224, 1, x_1);
lean_ctor_set(x_224, 2, x_2);
lean_ctor_set(x_224, 3, x_164);
lean_ctor_set(x_224, 4, x_164);
x_221 = x_224;
goto block_223;
}
block_223:
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_214);
lean_ctor_set(x_222, 2, x_215);
lean_ctor_set(x_222, 3, x_220);
lean_ctor_set(x_222, 4, x_221);
return x_222;
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_unsigned_to_nat(2u);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_1);
lean_ctor_set(x_238, 2, x_2);
lean_ctor_set(x_238, 3, x_3);
lean_ctor_set(x_238, 4, x_209);
return x_238;
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_4, 3);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_4, 4);
lean_inc(x_240);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_255; 
x_241 = lean_ctor_get(x_4, 0);
x_242 = lean_ctor_get(x_4, 1);
x_243 = lean_ctor_get(x_4, 2);
x_255 = !lean_is_exclusive(x_4);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_4, 4);
lean_dec(x_256);
x_257 = lean_ctor_get(x_4, 3);
lean_dec(x_257);
x_244 = x_4;
x_245 = x_255;
goto block_254;
}
else
{
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_4);
x_244 = lean_box(0);
x_245 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_246 = lean_ctor_get(x_239, 0);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_add(x_247, x_241);
lean_dec(x_241);
x_249 = lean_nat_add(x_247, x_246);
if (x_245 == 0)
{
lean_ctor_set(x_244, 4, x_239);
lean_ctor_set(x_244, 3, x_3);
lean_ctor_set(x_244, 2, x_2);
lean_ctor_set(x_244, 1, x_1);
lean_ctor_set(x_244, 0, x_249);
x_250 = x_244;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_1);
lean_ctor_set(x_253, 2, x_2);
lean_ctor_set(x_253, 3, x_3);
lean_ctor_set(x_253, 4, x_239);
x_250 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_242);
lean_ctor_set(x_251, 2, x_243);
lean_ctor_set(x_251, 3, x_250);
lean_ctor_set(x_251, 4, x_240);
return x_251;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_281; 
x_258 = lean_ctor_get(x_4, 1);
x_259 = lean_ctor_get(x_4, 2);
x_281 = !lean_is_exclusive(x_4);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_4, 4);
lean_dec(x_282);
x_283 = lean_ctor_get(x_4, 3);
lean_dec(x_283);
x_284 = lean_ctor_get(x_4, 0);
lean_dec(x_284);
x_260 = x_4;
x_261 = x_281;
goto block_280;
}
else
{
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_4);
x_260 = lean_box(0);
x_261 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_276; 
x_262 = lean_ctor_get(x_239, 1);
x_263 = lean_ctor_get(x_239, 2);
x_276 = !lean_is_exclusive(x_239);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_239, 4);
lean_dec(x_277);
x_278 = lean_ctor_get(x_239, 3);
lean_dec(x_278);
x_279 = lean_ctor_get(x_239, 0);
lean_dec(x_279);
x_264 = x_239;
x_265 = x_276;
goto block_275;
}
else
{
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_239);
x_264 = lean_box(0);
x_265 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_unsigned_to_nat(3u);
x_267 = lean_unsigned_to_nat(1u);
if (x_265 == 0)
{
lean_ctor_set(x_264, 4, x_240);
lean_ctor_set(x_264, 3, x_240);
lean_ctor_set(x_264, 2, x_2);
lean_ctor_set(x_264, 1, x_1);
lean_ctor_set(x_264, 0, x_267);
x_268 = x_264;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_1);
lean_ctor_set(x_274, 2, x_2);
lean_ctor_set(x_274, 3, x_240);
lean_ctor_set(x_274, 4, x_240);
x_268 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_269; 
if (x_261 == 0)
{
lean_ctor_set(x_260, 3, x_240);
lean_ctor_set(x_260, 0, x_267);
x_269 = x_260;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_258);
lean_ctor_set(x_272, 2, x_259);
lean_ctor_set(x_272, 3, x_240);
lean_ctor_set(x_272, 4, x_240);
x_269 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_262);
lean_ctor_set(x_270, 2, x_263);
lean_ctor_set(x_270, 3, x_268);
lean_ctor_set(x_270, 4, x_269);
return x_270;
}
}
}
}
}
}
else
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_4, 4);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_297; 
x_286 = lean_ctor_get(x_4, 1);
x_287 = lean_ctor_get(x_4, 2);
x_297 = !lean_is_exclusive(x_4);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_4, 4);
lean_dec(x_298);
x_299 = lean_ctor_get(x_4, 3);
lean_dec(x_299);
x_300 = lean_ctor_get(x_4, 0);
lean_dec(x_300);
x_288 = x_4;
x_289 = x_297;
goto block_296;
}
else
{
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_4);
x_288 = lean_box(0);
x_289 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_unsigned_to_nat(3u);
x_291 = lean_unsigned_to_nat(1u);
if (x_289 == 0)
{
lean_ctor_set(x_288, 4, x_239);
lean_ctor_set(x_288, 2, x_2);
lean_ctor_set(x_288, 1, x_1);
lean_ctor_set(x_288, 0, x_291);
x_292 = x_288;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_291);
lean_ctor_set(x_295, 1, x_1);
lean_ctor_set(x_295, 2, x_2);
lean_ctor_set(x_295, 3, x_239);
lean_ctor_set(x_295, 4, x_239);
x_292 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set(x_293, 4, x_285);
return x_293;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_unsigned_to_nat(2u);
x_302 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_1);
lean_ctor_set(x_302, 2, x_2);
lean_ctor_set(x_302, 3, x_285);
lean_ctor_set(x_302, 4, x_4);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_unsigned_to_nat(1u);
x_304 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_1);
lean_ctor_set(x_304, 2, x_2);
lean_ctor_set(x_304, 3, x_4);
lean_ctor_set(x_304, 4, x_4);
return x_304;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_unsigned_to_nat(393u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(22u);
x_3 = lean_unsigned_to_nat(394u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_unsigned_to_nat(383u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(22u);
x_3 = lean_unsigned_to_nat(384u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_mul(x_15, x_5);
x_17 = lean_nat_dec_lt(x_16, x_10);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
x_18 = lean_nat_mul(x_15, x_10);
x_19 = lean_nat_dec_lt(x_18, x_5);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_20, x_5);
x_22 = lean_nat_add(x_21, x_10);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 2, x_2);
lean_ctor_set(x_23, 3, x_3);
lean_ctor_set(x_23, 4, x_4);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_93; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_93 = !lean_is_exclusive(x_3);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_3, 4);
lean_dec(x_94);
x_95 = lean_ctor_get(x_3, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_3, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_3, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_3, 0);
lean_dec(x_98);
x_24 = x_3;
x_25 = x_93;
goto block_92;
}
else
{
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_93;
goto block_92;
}
block_92:
{
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 2);
x_30 = lean_ctor_get(x_9, 3);
x_31 = lean_ctor_get(x_9, 4);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_26);
x_34 = lean_nat_dec_lt(x_27, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; uint8_t x_73; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_73 = !lean_is_exclusive(x_9);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_9, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_9, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_9, 2);
lean_dec(x_76);
x_77 = lean_ctor_get(x_9, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_9, 0);
lean_dec(x_78);
x_35 = x_9;
x_36 = x_73;
goto block_72;
}
else
{
lean_dec(x_9);
x_35 = lean_box(0);
x_36 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_60; lean_object* x_61; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_37, x_5);
lean_dec(x_5);
x_39 = lean_nat_add(x_38, x_10);
lean_dec(x_38);
x_60 = lean_nat_add(x_37, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_30, 0);
lean_inc(x_70);
x_61 = x_70;
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = lean_unsigned_to_nat(0u);
x_61 = x_71;
goto block_69;
}
block_59:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_nat_add(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
lean_inc_ref(x_4);
if (x_36 == 0)
{
lean_ctor_set(x_35, 4, x_4);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 2, x_2);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set(x_35, 0, x_43);
x_44 = x_35;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_2);
lean_ctor_set(x_58, 3, x_31);
lean_ctor_set(x_58, 4, x_4);
x_44 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_45; uint8_t x_46; uint8_t x_51; 
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_4, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_4, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_4, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_4, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_4, 0);
lean_dec(x_56);
x_45 = x_4;
x_46 = x_51;
goto block_50;
}
else
{
lean_dec(x_4);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 2, x_29);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 0, x_39);
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_28);
lean_ctor_set(x_49, 2, x_29);
lean_ctor_set(x_49, 3, x_41);
lean_ctor_set(x_49, 4, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
block_69:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_nat_add(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_30);
lean_ctor_set(x_24, 0, x_62);
x_63 = x_24;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_6);
lean_ctor_set(x_68, 2, x_7);
lean_ctor_set(x_68, 3, x_8);
lean_ctor_set(x_68, 4, x_30);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
x_64 = lean_nat_add(x_37, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
x_40 = x_64;
x_41 = x_63;
x_42 = x_65;
goto block_59;
}
else
{
lean_object* x_66; 
x_66 = lean_unsigned_to_nat(0u);
x_40 = x_64;
x_41 = x_63;
x_42 = x_66;
goto block_59;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_79, x_5);
lean_dec(x_5);
x_81 = lean_nat_add(x_80, x_10);
lean_dec(x_80);
x_82 = lean_nat_add(x_79, x_10);
x_83 = lean_nat_add(x_82, x_27);
lean_dec(x_82);
if (x_25 == 0)
{
lean_ctor_set(x_24, 4, x_4);
lean_ctor_set(x_24, 3, x_9);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 0, x_83);
x_84 = x_24;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_1);
lean_ctor_set(x_87, 2, x_2);
lean_ctor_set(x_87, 3, x_9);
lean_ctor_set(x_87, 4, x_4);
x_84 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_6);
lean_ctor_set(x_85, 2, x_7);
lean_ctor_set(x_85, 3, x_8);
lean_ctor_set(x_85, 4, x_84);
return x_85;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_8);
lean_del_object(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2);
x_89 = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_del_object(x_24);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3);
x_91 = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_99; uint8_t x_100; uint8_t x_166; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_166 = !lean_is_exclusive(x_4);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_4, 4);
lean_dec(x_167);
x_168 = lean_ctor_get(x_4, 3);
lean_dec(x_168);
x_169 = lean_ctor_get(x_4, 2);
lean_dec(x_169);
x_170 = lean_ctor_get(x_4, 1);
lean_dec(x_170);
x_171 = lean_ctor_get(x_4, 0);
lean_dec(x_171);
x_99 = x_4;
x_100 = x_166;
goto block_165;
}
else
{
lean_dec(x_4);
x_99 = lean_box(0);
x_100 = x_166;
goto block_165;
}
block_165:
{
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_101 = lean_ctor_get(x_13, 0);
x_102 = lean_ctor_get(x_13, 1);
x_103 = lean_ctor_get(x_13, 2);
x_104 = lean_ctor_get(x_13, 3);
x_105 = lean_ctor_get(x_13, 4);
x_106 = lean_ctor_get(x_14, 0);
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_nat_mul(x_107, x_106);
x_109 = lean_nat_dec_lt(x_101, x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; uint8_t x_136; 
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
x_136 = !lean_is_exclusive(x_13);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_13, 4);
lean_dec(x_137);
x_138 = lean_ctor_get(x_13, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_13, 2);
lean_dec(x_139);
x_140 = lean_ctor_get(x_13, 1);
lean_dec(x_140);
x_141 = lean_ctor_get(x_13, 0);
lean_dec(x_141);
x_110 = x_13;
x_111 = x_136;
goto block_135;
}
else
{
lean_dec(x_13);
x_110 = lean_box(0);
x_111 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_126; 
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_112, x_5);
x_114 = lean_nat_add(x_113, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_104, 0);
lean_inc(x_133);
x_126 = x_133;
goto block_132;
}
else
{
lean_object* x_134; 
x_134 = lean_unsigned_to_nat(0u);
x_126 = x_134;
goto block_132;
}
block_125:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_nat_add(x_116, x_117);
lean_dec(x_117);
lean_dec(x_116);
if (x_111 == 0)
{
lean_ctor_set(x_110, 4, x_14);
lean_ctor_set(x_110, 3, x_105);
lean_ctor_set(x_110, 2, x_12);
lean_ctor_set(x_110, 1, x_11);
lean_ctor_set(x_110, 0, x_118);
x_119 = x_110;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_11);
lean_ctor_set(x_124, 2, x_12);
lean_ctor_set(x_124, 3, x_105);
lean_ctor_set(x_124, 4, x_14);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_100 == 0)
{
lean_ctor_set(x_99, 4, x_119);
lean_ctor_set(x_99, 3, x_115);
lean_ctor_set(x_99, 2, x_103);
lean_ctor_set(x_99, 1, x_102);
lean_ctor_set(x_99, 0, x_114);
x_120 = x_99;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_102);
lean_ctor_set(x_122, 2, x_103);
lean_ctor_set(x_122, 3, x_115);
lean_ctor_set(x_122, 4, x_119);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
block_132:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_nat_add(x_113, x_126);
lean_dec(x_126);
lean_dec(x_113);
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_1);
lean_ctor_set(x_128, 2, x_2);
lean_ctor_set(x_128, 3, x_3);
lean_ctor_set(x_128, 4, x_104);
x_129 = lean_nat_add(x_112, x_106);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_105, 0);
lean_inc(x_130);
x_115 = x_128;
x_116 = x_129;
x_117 = x_130;
goto block_125;
}
else
{
lean_object* x_131; 
x_131 = lean_unsigned_to_nat(0u);
x_115 = x_128;
x_116 = x_129;
x_117 = x_131;
goto block_125;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_142, x_5);
x_144 = lean_nat_add(x_143, x_10);
lean_dec(x_10);
x_145 = lean_nat_add(x_143, x_101);
lean_dec(x_143);
lean_inc_ref(x_3);
if (x_100 == 0)
{
lean_ctor_set(x_99, 4, x_13);
lean_ctor_set(x_99, 3, x_3);
lean_ctor_set(x_99, 2, x_2);
lean_ctor_set(x_99, 1, x_1);
lean_ctor_set(x_99, 0, x_145);
x_146 = x_99;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_145);
lean_ctor_set(x_160, 1, x_1);
lean_ctor_set(x_160, 2, x_2);
lean_ctor_set(x_160, 3, x_3);
lean_ctor_set(x_160, 4, x_13);
x_146 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_147; uint8_t x_148; uint8_t x_153; 
x_153 = !lean_is_exclusive(x_3);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_3, 4);
lean_dec(x_154);
x_155 = lean_ctor_get(x_3, 3);
lean_dec(x_155);
x_156 = lean_ctor_get(x_3, 2);
lean_dec(x_156);
x_157 = lean_ctor_get(x_3, 1);
lean_dec(x_157);
x_158 = lean_ctor_get(x_3, 0);
lean_dec(x_158);
x_147 = x_3;
x_148 = x_153;
goto block_152;
}
else
{
lean_dec(x_3);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 4, x_14);
lean_ctor_set(x_147, 3, x_146);
lean_ctor_set(x_147, 2, x_12);
lean_ctor_set(x_147, 1, x_11);
lean_ctor_set(x_147, 0, x_144);
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_11);
lean_ctor_set(x_151, 2, x_12);
lean_ctor_set(x_151, 3, x_146);
lean_ctor_set(x_151, 4, x_14);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_13);
lean_del_object(x_99);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4);
x_162 = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(x_161);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_del_object(x_99);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5);
x_164 = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(x_163);
return x_164;
}
}
}
}
else
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_3, 4);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; uint8_t x_199; 
x_174 = lean_ctor_get(x_3, 0);
x_175 = lean_ctor_get(x_3, 1);
x_176 = lean_ctor_get(x_3, 2);
x_199 = !lean_is_exclusive(x_3);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_3, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_3, 3);
lean_dec(x_201);
x_177 = x_3;
x_178 = x_199;
goto block_198;
}
else
{
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_3);
x_177 = lean_box(0);
x_178 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_173, 0);
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_nat_add(x_180, x_174);
lean_dec(x_174);
x_182 = lean_nat_add(x_180, x_179);
lean_inc_ref(x_173);
if (x_178 == 0)
{
lean_ctor_set(x_177, 4, x_4);
lean_ctor_set(x_177, 3, x_173);
lean_ctor_set(x_177, 2, x_2);
lean_ctor_set(x_177, 1, x_1);
lean_ctor_set(x_177, 0, x_182);
x_183 = x_177;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_197, 0, x_182);
lean_ctor_set(x_197, 1, x_1);
lean_ctor_set(x_197, 2, x_2);
lean_ctor_set(x_197, 3, x_173);
lean_ctor_set(x_197, 4, x_4);
x_183 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_184; uint8_t x_185; uint8_t x_190; 
x_190 = !lean_is_exclusive(x_173);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_173, 4);
lean_dec(x_191);
x_192 = lean_ctor_get(x_173, 3);
lean_dec(x_192);
x_193 = lean_ctor_get(x_173, 2);
lean_dec(x_193);
x_194 = lean_ctor_get(x_173, 1);
lean_dec(x_194);
x_195 = lean_ctor_get(x_173, 0);
lean_dec(x_195);
x_184 = x_173;
x_185 = x_190;
goto block_189;
}
else
{
lean_dec(x_173);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
lean_ctor_set(x_184, 4, x_183);
lean_ctor_set(x_184, 3, x_172);
lean_ctor_set(x_184, 2, x_176);
lean_ctor_set(x_184, 1, x_175);
lean_ctor_set(x_184, 0, x_181);
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_175);
lean_ctor_set(x_188, 2, x_176);
lean_ctor_set(x_188, 3, x_172);
lean_ctor_set(x_188, 4, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_213; 
x_202 = lean_ctor_get(x_3, 1);
x_203 = lean_ctor_get(x_3, 2);
x_213 = !lean_is_exclusive(x_3);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_3, 4);
lean_dec(x_214);
x_215 = lean_ctor_get(x_3, 3);
lean_dec(x_215);
x_216 = lean_ctor_get(x_3, 0);
lean_dec(x_216);
x_204 = x_3;
x_205 = x_213;
goto block_212;
}
else
{
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_3);
x_204 = lean_box(0);
x_205 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_unsigned_to_nat(3u);
x_207 = lean_unsigned_to_nat(1u);
if (x_205 == 0)
{
lean_ctor_set(x_204, 3, x_173);
lean_ctor_set(x_204, 2, x_2);
lean_ctor_set(x_204, 1, x_1);
lean_ctor_set(x_204, 0, x_207);
x_208 = x_204;
goto block_210;
}
else
{
lean_object* x_211; 
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_1);
lean_ctor_set(x_211, 2, x_2);
lean_ctor_set(x_211, 3, x_173);
lean_ctor_set(x_211, 4, x_173);
x_208 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_202);
lean_ctor_set(x_209, 2, x_203);
lean_ctor_set(x_209, 3, x_172);
lean_ctor_set(x_209, 4, x_208);
return x_209;
}
}
}
}
else
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_3, 4);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_241; 
lean_inc(x_172);
x_218 = lean_ctor_get(x_3, 1);
x_219 = lean_ctor_get(x_3, 2);
x_241 = !lean_is_exclusive(x_3);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_3, 4);
lean_dec(x_242);
x_243 = lean_ctor_get(x_3, 3);
lean_dec(x_243);
x_244 = lean_ctor_get(x_3, 0);
lean_dec(x_244);
x_220 = x_3;
x_221 = x_241;
goto block_240;
}
else
{
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_3);
x_220 = lean_box(0);
x_221 = x_241;
goto block_240;
}
block_240:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; uint8_t x_236; 
x_222 = lean_ctor_get(x_217, 1);
x_223 = lean_ctor_get(x_217, 2);
x_236 = !lean_is_exclusive(x_217);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_217, 4);
lean_dec(x_237);
x_238 = lean_ctor_get(x_217, 3);
lean_dec(x_238);
x_239 = lean_ctor_get(x_217, 0);
lean_dec(x_239);
x_224 = x_217;
x_225 = x_236;
goto block_235;
}
else
{
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_217);
x_224 = lean_box(0);
x_225 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_unsigned_to_nat(3u);
x_227 = lean_unsigned_to_nat(1u);
if (x_225 == 0)
{
lean_ctor_set(x_224, 4, x_172);
lean_ctor_set(x_224, 3, x_172);
lean_ctor_set(x_224, 2, x_219);
lean_ctor_set(x_224, 1, x_218);
lean_ctor_set(x_224, 0, x_227);
x_228 = x_224;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_227);
lean_ctor_set(x_234, 1, x_218);
lean_ctor_set(x_234, 2, x_219);
lean_ctor_set(x_234, 3, x_172);
lean_ctor_set(x_234, 4, x_172);
x_228 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_229; 
if (x_221 == 0)
{
lean_ctor_set(x_220, 4, x_172);
lean_ctor_set(x_220, 2, x_2);
lean_ctor_set(x_220, 1, x_1);
lean_ctor_set(x_220, 0, x_227);
x_229 = x_220;
goto block_231;
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_232, 0, x_227);
lean_ctor_set(x_232, 1, x_1);
lean_ctor_set(x_232, 2, x_2);
lean_ctor_set(x_232, 3, x_172);
lean_ctor_set(x_232, 4, x_172);
x_229 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_222);
lean_ctor_set(x_230, 2, x_223);
lean_ctor_set(x_230, 3, x_228);
lean_ctor_set(x_230, 4, x_229);
return x_230;
}
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_unsigned_to_nat(2u);
x_246 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_1);
lean_ctor_set(x_246, 2, x_2);
lean_ctor_set(x_246, 3, x_3);
lean_ctor_set(x_246, 4, x_217);
return x_246;
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_4, 3);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_4, 4);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_263; 
x_249 = lean_ctor_get(x_4, 0);
x_250 = lean_ctor_get(x_4, 1);
x_251 = lean_ctor_get(x_4, 2);
x_263 = !lean_is_exclusive(x_4);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_4, 4);
lean_dec(x_264);
x_265 = lean_ctor_get(x_4, 3);
lean_dec(x_265);
x_252 = x_4;
x_253 = x_263;
goto block_262;
}
else
{
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_4);
x_252 = lean_box(0);
x_253 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_247, 0);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_add(x_255, x_249);
lean_dec(x_249);
x_257 = lean_nat_add(x_255, x_254);
if (x_253 == 0)
{
lean_ctor_set(x_252, 4, x_247);
lean_ctor_set(x_252, 3, x_3);
lean_ctor_set(x_252, 2, x_2);
lean_ctor_set(x_252, 1, x_1);
lean_ctor_set(x_252, 0, x_257);
x_258 = x_252;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_257);
lean_ctor_set(x_261, 1, x_1);
lean_ctor_set(x_261, 2, x_2);
lean_ctor_set(x_261, 3, x_3);
lean_ctor_set(x_261, 4, x_247);
x_258 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_250);
lean_ctor_set(x_259, 2, x_251);
lean_ctor_set(x_259, 3, x_258);
lean_ctor_set(x_259, 4, x_248);
return x_259;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_289; 
x_266 = lean_ctor_get(x_4, 1);
x_267 = lean_ctor_get(x_4, 2);
x_289 = !lean_is_exclusive(x_4);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_4, 4);
lean_dec(x_290);
x_291 = lean_ctor_get(x_4, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_4, 0);
lean_dec(x_292);
x_268 = x_4;
x_269 = x_289;
goto block_288;
}
else
{
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_4);
x_268 = lean_box(0);
x_269 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_284; 
x_270 = lean_ctor_get(x_247, 1);
x_271 = lean_ctor_get(x_247, 2);
x_284 = !lean_is_exclusive(x_247);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_247, 4);
lean_dec(x_285);
x_286 = lean_ctor_get(x_247, 3);
lean_dec(x_286);
x_287 = lean_ctor_get(x_247, 0);
lean_dec(x_287);
x_272 = x_247;
x_273 = x_284;
goto block_283;
}
else
{
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_247);
x_272 = lean_box(0);
x_273 = x_284;
goto block_283;
}
block_283:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_unsigned_to_nat(3u);
x_275 = lean_unsigned_to_nat(1u);
if (x_273 == 0)
{
lean_ctor_set(x_272, 4, x_248);
lean_ctor_set(x_272, 3, x_248);
lean_ctor_set(x_272, 2, x_2);
lean_ctor_set(x_272, 1, x_1);
lean_ctor_set(x_272, 0, x_275);
x_276 = x_272;
goto block_281;
}
else
{
lean_object* x_282; 
x_282 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_282, 0, x_275);
lean_ctor_set(x_282, 1, x_1);
lean_ctor_set(x_282, 2, x_2);
lean_ctor_set(x_282, 3, x_248);
lean_ctor_set(x_282, 4, x_248);
x_276 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_277; 
if (x_269 == 0)
{
lean_ctor_set(x_268, 3, x_248);
lean_ctor_set(x_268, 0, x_275);
x_277 = x_268;
goto block_279;
}
else
{
lean_object* x_280; 
x_280 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_280, 0, x_275);
lean_ctor_set(x_280, 1, x_266);
lean_ctor_set(x_280, 2, x_267);
lean_ctor_set(x_280, 3, x_248);
lean_ctor_set(x_280, 4, x_248);
x_277 = x_280;
goto block_279;
}
block_279:
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_278, 0, x_274);
lean_ctor_set(x_278, 1, x_270);
lean_ctor_set(x_278, 2, x_271);
lean_ctor_set(x_278, 3, x_276);
lean_ctor_set(x_278, 4, x_277);
return x_278;
}
}
}
}
}
}
else
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_4, 4);
lean_inc(x_293);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_305; 
x_294 = lean_ctor_get(x_4, 1);
x_295 = lean_ctor_get(x_4, 2);
x_305 = !lean_is_exclusive(x_4);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_4, 4);
lean_dec(x_306);
x_307 = lean_ctor_get(x_4, 3);
lean_dec(x_307);
x_308 = lean_ctor_get(x_4, 0);
lean_dec(x_308);
x_296 = x_4;
x_297 = x_305;
goto block_304;
}
else
{
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_4);
x_296 = lean_box(0);
x_297 = x_305;
goto block_304;
}
block_304:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_unsigned_to_nat(3u);
x_299 = lean_unsigned_to_nat(1u);
if (x_297 == 0)
{
lean_ctor_set(x_296, 4, x_247);
lean_ctor_set(x_296, 2, x_2);
lean_ctor_set(x_296, 1, x_1);
lean_ctor_set(x_296, 0, x_299);
x_300 = x_296;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_1);
lean_ctor_set(x_303, 2, x_2);
lean_ctor_set(x_303, 3, x_247);
lean_ctor_set(x_303, 4, x_247);
x_300 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_300);
lean_ctor_set(x_301, 4, x_293);
return x_301;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_unsigned_to_nat(2u);
x_310 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_1);
lean_ctor_set(x_310, 2, x_2);
lean_ctor_set(x_310, 3, x_293);
lean_ctor_set(x_310, 4, x_4);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_unsigned_to_nat(1u);
x_312 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_1);
lean_ctor_set(x_312, 2, x_2);
lean_ctor_set(x_312, 3, x_4);
lean_ctor_set(x_312, 4, x_4);
return x_312;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_10 = x_16;
goto block_15;
}
else
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(0u);
x_10 = x_17;
goto block_15;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_3);
lean_ctor_set(x_8, 4, x_4);
return x_8;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_5 = x_12;
x_6 = x_13;
goto block_9;
}
else
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(0u);
x_5 = x_12;
x_6 = x_14;
goto block_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_1, x_2, x_3, x_6);
x_9 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_singleL___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_1, x_2, x_6, x_7);
x_9 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_singleR___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_1, x_2, x_3, x_8);
x_12 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_4, x_5, x_9, x_10);
x_13 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_6, x_7, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_DTreeMap_Internal_Impl_doubleL___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_3, x_4, x_5, x_8);
x_12 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_1, x_2, x_9, x_10);
x_13 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_6, x_7, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_DTreeMap_Internal_Impl_doubleR___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_21; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
x_21 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(0u);
x_21 = x_27;
goto block_25;
}
block_20:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_mul(x_8, x_10);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
if (x_12 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
lean_dec_ref(x_6);
x_17 = l_Std_DTreeMap_Internal_Impl_doubleL___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_15, x_16, x_7);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Std_DTreeMap_Internal_Impl_singleL___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = l_Std_DTreeMap_Internal_Impl_singleL___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
block_25:
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(2u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
x_8 = x_22;
x_9 = x_21;
x_10 = x_23;
goto block_20;
}
else
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(0u);
x_8 = x_22;
x_9 = x_21;
x_10 = x_24;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_rotateL___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_21; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
x_21 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(0u);
x_21 = x_27;
goto block_25;
}
block_20:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_mul(x_9, x_10);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (x_12 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
lean_dec_ref(x_6);
x_17 = l_Std_DTreeMap_Internal_Impl_doubleR___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_15, x_16, x_7);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Std_DTreeMap_Internal_Impl_singleR___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = l_Std_DTreeMap_Internal_Impl_singleR___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
block_25:
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(2u);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_8 = x_21;
x_9 = x_22;
x_10 = x_23;
goto block_20;
}
else
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(0u);
x_8 = x_21;
x_9 = x_22;
x_10 = x_24;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_rotateR___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_28; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
x_28 = x_32;
goto block_31;
}
else
{
lean_object* x_33; 
x_33 = lean_unsigned_to_nat(0u);
x_28 = x_33;
goto block_31;
}
block_27:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_nat_add(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_le(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_mul(x_10, x_5);
x_12 = lean_nat_dec_lt(x_11, x_6);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_nat_mul(x_10, x_6);
lean_dec(x_6);
x_14 = lean_nat_dec_lt(x_13, x_5);
lean_dec(x_5);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_1, x_2, x_3, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 4);
lean_inc(x_19);
lean_dec(x_3);
x_20 = l_Std_DTreeMap_Internal_Impl_rotateR___redArg(x_1, x_2, x_16, x_17, x_18, x_19, x_4);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 4);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l_Std_DTreeMap_Internal_Impl_rotateL___redArg(x_1, x_2, x_3, x_21, x_22, x_23, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
x_26 = l_Std_DTreeMap_Internal_Impl_bin___redArg(x_1, x_2, x_3, x_4);
return x_26;
}
}
block_31:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_5 = x_28;
x_6 = x_29;
goto block_27;
}
else
{
lean_object* x_30; 
x_30 = lean_unsigned_to_nat(0u);
x_5 = x_28;
x_6 = x_30;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_balance_u2098___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc_ref(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
lean_dec_ref(x_8);
x_22 = lean_apply_13(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
lean_dec_ref(x_7);
x_31 = lean_apply_8(x_5, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_32);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 4);
lean_inc(x_40);
lean_dec_ref(x_32);
x_41 = lean_apply_8(x_4, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec_ref(x_1);
x_45 = lean_apply_3(x_3, x_42, x_43, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_box(0);
x_47 = lean_apply_1(x_2, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_inc_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_dec_ref(x_4);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 4);
lean_inc(x_19);
lean_dec_ref(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 4);
lean_inc(x_24);
lean_dec_ref(x_11);
x_25 = lean_apply_13(x_9, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
lean_dec_ref(x_4);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 4);
lean_inc(x_33);
lean_dec_ref(x_10);
x_34 = lean_apply_8(x_8, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
x_35 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_35);
lean_dec(x_6);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
lean_dec_ref(x_4);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 4);
lean_inc(x_43);
lean_dec_ref(x_35);
x_44 = lean_apply_8(x_7, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_7);
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 2);
lean_inc(x_47);
lean_dec_ref(x_4);
x_48 = lean_apply_3(x_6, x_45, x_46, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = lean_box(0);
x_50 = lean_apply_1(x_5, x_49);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 4);
lean_inc(x_16);
lean_dec_ref(x_2);
x_17 = lean_apply_10(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_dec_ref(x_1);
x_23 = lean_apply_5(x_5, x_18, x_19, x_20, x_21, x_22);
return x_23;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 4);
lean_inc(x_28);
lean_dec_ref(x_2);
x_29 = lean_apply_5(x_4, x_24, x_25, x_26, x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_apply_1(x_3, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = lean_apply_10(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_apply_1(x_5, x_2);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___redArg(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc_ref(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
lean_dec_ref(x_8);
x_22 = lean_apply_15(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0), lean_box(0));
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
lean_dec_ref(x_7);
x_31 = lean_apply_10(x_5, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, lean_box(0), lean_box(0));
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_32);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 4);
lean_inc(x_40);
lean_dec_ref(x_32);
x_41 = lean_apply_10(x_4, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, lean_box(0), lean_box(0));
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec_ref(x_1);
x_45 = lean_apply_5(x_3, x_42, x_43, x_44, lean_box(0), lean_box(0));
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_inc_ref(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_dec_ref(x_4);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 4);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 4);
lean_inc(x_26);
lean_dec_ref(x_13);
x_27 = lean_apply_15(x_11, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, lean_box(0), lean_box(0));
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
lean_dec_ref(x_4);
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 4);
lean_inc(x_35);
lean_dec_ref(x_12);
x_36 = lean_apply_10(x_10, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, lean_box(0), lean_box(0));
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
x_37 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_37);
lean_dec(x_8);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_dec_ref(x_4);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 4);
lean_inc(x_45);
lean_dec_ref(x_37);
x_46 = lean_apply_10(x_9, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, lean_box(0), lean_box(0));
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
x_47 = lean_ctor_get(x_4, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec_ref(x_4);
x_50 = lean_apply_5(x_8, x_47, x_48, x_49, lean_box(0), lean_box(0));
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = lean_apply_2(x_7, lean_box(0), lean_box(0));
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___redArg(x_9, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = lean_apply_12(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, lean_box(0), lean_box(0));
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_apply_7(x_4, x_17, x_18, x_19, x_20, x_21, lean_box(0), lean_box(0));
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___redArg(x_12, x_13, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc_ref(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
lean_dec_ref(x_8);
x_22 = lean_apply_13(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
lean_dec_ref(x_7);
x_31 = lean_apply_8(x_5, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_32);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 4);
lean_inc(x_40);
lean_dec_ref(x_32);
x_41 = lean_apply_8(x_4, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec_ref(x_1);
x_45 = lean_apply_3(x_3, x_42, x_43, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_box(0);
x_47 = lean_apply_1(x_2, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_inc_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_dec_ref(x_4);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 4);
lean_inc(x_19);
lean_dec_ref(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 4);
lean_inc(x_24);
lean_dec_ref(x_11);
x_25 = lean_apply_13(x_9, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
lean_dec_ref(x_4);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 4);
lean_inc(x_33);
lean_dec_ref(x_10);
x_34 = lean_apply_8(x_8, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
x_35 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_35);
lean_dec(x_6);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
lean_dec_ref(x_4);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 4);
lean_inc(x_43);
lean_dec_ref(x_35);
x_44 = lean_apply_8(x_7, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_7);
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 2);
lean_inc(x_47);
lean_dec_ref(x_4);
x_48 = lean_apply_3(x_6, x_45, x_46, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = lean_box(0);
x_50 = lean_apply_1(x_5, x_49);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = lean_apply_12(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, lean_box(0), lean_box(0));
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_apply_7(x_4, x_17, x_18, x_19, x_20, x_21, lean_box(0), lean_box(0));
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___redArg(x_12, x_13, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc_ref(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
lean_dec_ref(x_8);
x_22 = lean_apply_15(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0), lean_box(0));
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
lean_dec_ref(x_7);
x_31 = lean_apply_10(x_5, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, lean_box(0), lean_box(0));
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_32);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 4);
lean_inc(x_40);
lean_dec_ref(x_32);
x_41 = lean_apply_10(x_4, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, lean_box(0), lean_box(0));
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec_ref(x_1);
x_45 = lean_apply_5(x_3, x_42, x_43, x_44, lean_box(0), lean_box(0));
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_inc_ref(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_dec_ref(x_4);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 4);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 4);
lean_inc(x_26);
lean_dec_ref(x_13);
x_27 = lean_apply_15(x_11, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, lean_box(0), lean_box(0));
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
lean_dec_ref(x_4);
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 4);
lean_inc(x_35);
lean_dec_ref(x_12);
x_36 = lean_apply_10(x_10, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, lean_box(0), lean_box(0));
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
x_37 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_37);
lean_dec(x_8);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_dec_ref(x_4);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 4);
lean_inc(x_45);
lean_dec_ref(x_37);
x_46 = lean_apply_10(x_9, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, lean_box(0), lean_box(0));
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
x_47 = lean_ctor_get(x_4, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec_ref(x_4);
x_50 = lean_apply_5(x_8, x_47, x_48, x_49, lean_box(0), lean_box(0));
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = lean_apply_2(x_7, lean_box(0), lean_box(0));
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___redArg(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc_ref(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
lean_dec_ref(x_8);
x_22 = lean_apply_15(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0), lean_box(0));
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
lean_dec_ref(x_7);
x_31 = lean_apply_10(x_5, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, lean_box(0), lean_box(0));
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_32);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 4);
lean_inc(x_40);
lean_dec_ref(x_32);
x_41 = lean_apply_10(x_4, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, lean_box(0), lean_box(0));
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec_ref(x_1);
x_45 = lean_apply_5(x_3, x_42, x_43, x_44, lean_box(0), lean_box(0));
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_inc_ref(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_dec_ref(x_4);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 4);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 4);
lean_inc(x_26);
lean_dec_ref(x_13);
x_27 = lean_apply_15(x_11, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, lean_box(0), lean_box(0));
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
lean_dec_ref(x_4);
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 4);
lean_inc(x_35);
lean_dec_ref(x_12);
x_36 = lean_apply_10(x_10, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, lean_box(0), lean_box(0));
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
x_37 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_37);
lean_dec(x_8);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_dec_ref(x_4);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 4);
lean_inc(x_45);
lean_dec_ref(x_37);
x_46 = lean_apply_10(x_9, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, lean_box(0), lean_box(0));
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
x_47 = lean_ctor_get(x_4, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec_ref(x_4);
x_50 = lean_apply_5(x_8, x_47, x_48, x_49, lean_box(0), lean_box(0));
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = lean_apply_2(x_7, lean_box(0), lean_box(0));
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___redArg(x_9, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc_ref(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
lean_dec_ref(x_8);
x_22 = lean_apply_13(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
lean_dec_ref(x_7);
x_31 = lean_apply_8(x_5, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_32);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 4);
lean_inc(x_40);
lean_dec_ref(x_32);
x_41 = lean_apply_8(x_4, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec_ref(x_1);
x_45 = lean_apply_3(x_3, x_42, x_43, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_box(0);
x_47 = lean_apply_1(x_2, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_inc_ref(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_dec_ref(x_4);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 4);
lean_inc(x_19);
lean_dec_ref(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 4);
lean_inc(x_24);
lean_dec_ref(x_11);
x_25 = lean_apply_13(x_9, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
lean_dec_ref(x_4);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 4);
lean_inc(x_33);
lean_dec_ref(x_10);
x_34 = lean_apply_8(x_8, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
x_35 = lean_ctor_get(x_4, 4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_35);
lean_dec(x_6);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
lean_dec_ref(x_4);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 4);
lean_inc(x_43);
lean_dec_ref(x_35);
x_44 = lean_apply_8(x_7, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_7);
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 2);
lean_inc(x_47);
lean_dec_ref(x_4);
x_48 = lean_apply_3(x_6, x_45, x_46, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = lean_box(0);
x_50 = lean_apply_1(x_5, x_49);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_1(x_2, lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Balanced(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Balancing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Ord_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Balanced(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_Balancing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Balanced(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Balancing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Balanced(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Balancing(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Balancing(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Balancing(builtin);
}
#ifdef __cplusplus
}
#endif
