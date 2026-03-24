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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35;
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
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4;
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
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Array_mkArray0(lean_box(0));
return v___x_53_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__34));
v___x_102_ = l_String_toRawSubstring_x27(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__64));
v___x_166_ = l_String_toRawSubstring_x27(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1(lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5));
v___x_201_ = l_Lean_Syntax_isOfKind(v_x_197_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref(v_a_198_);
v___x_202_ = lean_box(1);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_a_199_);
return v___x_203_;
}
else
{
lean_object* v_quotContext_204_; lean_object* v_currMacroScope_205_; lean_object* v_ref_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_quotContext_204_ = lean_ctor_get(v_a_198_, 1);
lean_inc(v_quotContext_204_);
v_currMacroScope_205_ = lean_ctor_get(v_a_198_, 2);
lean_inc(v_currMacroScope_205_);
v_ref_206_ = lean_ctor_get(v_a_198_, 5);
lean_inc(v_ref_206_);
lean_dec_ref(v_a_198_);
v___x_207_ = 0;
v___x_208_ = l_Lean_SourceInfo_fromRef(v_ref_206_, v___x_207_);
lean_dec(v_ref_206_);
v___x_209_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4));
v___x_210_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__5));
lean_inc(v___x_208_);
v___x_211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_208_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7));
v___x_213_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9));
v___x_214_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11));
v___x_215_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13));
v___x_216_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__14));
lean_inc(v___x_208_);
v___x_217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_208_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
lean_inc(v___x_208_);
v___x_218_ = l_Lean_Syntax_node1(v___x_208_, v___x_215_, v___x_217_);
v___x_219_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15);
lean_inc(v___x_208_);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_208_);
lean_ctor_set(v___x_220_, 1, v___x_214_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__16));
v___x_222_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17));
lean_inc(v___x_208_);
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_208_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
v___x_224_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__18));
v___x_225_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19));
lean_inc(v___x_208_);
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_208_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_inc_ref_n(v___x_220_, 2);
lean_inc(v___x_208_);
v___x_227_ = l_Lean_Syntax_node3(v___x_208_, v___x_225_, v___x_226_, v___x_220_, v___x_220_);
lean_inc(v___x_208_);
v___x_228_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_227_);
lean_inc(v___x_208_);
v___x_229_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_228_);
lean_inc(v___x_208_);
v___x_230_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_229_);
lean_inc_ref(v___x_223_);
lean_inc(v___x_208_);
v___x_231_ = l_Lean_Syntax_node2(v___x_208_, v___x_222_, v___x_223_, v___x_230_);
v___x_232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21));
v___x_233_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__22));
lean_inc(v___x_208_);
v___x_234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_208_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24));
v___x_236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__25));
lean_inc(v___x_208_);
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_208_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__26));
v___x_239_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27));
lean_inc(v___x_208_);
v___x_240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_208_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
v___x_241_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29));
lean_inc_ref(v___x_220_);
lean_inc(v___x_208_);
v___x_242_ = l_Lean_Syntax_node1(v___x_208_, v___x_241_, v___x_220_);
v___x_243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__30));
lean_inc(v___x_208_);
v___x_244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_208_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
lean_inc(v___x_208_);
v___x_245_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_244_);
v___x_246_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__31));
lean_inc(v___x_208_);
v___x_247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_208_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33));
v___x_249_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35);
v___x_250_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36));
lean_inc(v_currMacroScope_205_);
lean_inc(v_quotContext_204_);
v___x_251_ = l_Lean_addMacroScope(v_quotContext_204_, v___x_250_, v_currMacroScope_205_);
v___x_252_ = lean_box(0);
lean_inc(v___x_208_);
v___x_253_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_253_, 0, v___x_208_);
lean_ctor_set(v___x_253_, 1, v___x_249_);
lean_ctor_set(v___x_253_, 2, v___x_251_);
lean_ctor_set(v___x_253_, 3, v___x_252_);
lean_inc_ref_n(v___x_220_, 2);
lean_inc(v___x_208_);
v___x_254_ = l_Lean_Syntax_node3(v___x_208_, v___x_248_, v___x_220_, v___x_220_, v___x_253_);
lean_inc(v___x_208_);
v___x_255_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_254_);
v___x_256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__37));
lean_inc(v___x_208_);
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_208_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_inc(v___x_208_);
v___x_258_ = l_Lean_Syntax_node3(v___x_208_, v___x_214_, v___x_247_, v___x_255_, v___x_257_);
v___x_259_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39));
v___x_260_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__40));
lean_inc(v___x_208_);
v___x_261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_208_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42));
v___x_263_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__43));
lean_inc(v___x_208_);
v___x_264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_208_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_inc(v___x_208_);
v___x_265_ = l_Lean_Syntax_node1(v___x_208_, v___x_262_, v___x_264_);
lean_inc(v___x_208_);
v___x_266_ = l_Lean_Syntax_node2(v___x_208_, v___x_259_, v___x_261_, v___x_265_);
lean_inc(v___x_208_);
v___x_267_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_266_);
lean_inc_ref(v___x_220_);
lean_inc(v___x_242_);
lean_inc(v___x_208_);
v___x_268_ = l_Lean_Syntax_node6(v___x_208_, v___x_239_, v___x_240_, v___x_242_, v___x_220_, v___x_245_, v___x_258_, v___x_267_);
lean_inc(v___x_208_);
v___x_269_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_268_);
lean_inc(v___x_208_);
v___x_270_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_269_);
lean_inc(v___x_208_);
v___x_271_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_270_);
lean_inc_ref(v___x_237_);
lean_inc(v___x_208_);
v___x_272_ = l_Lean_Syntax_node2(v___x_208_, v___x_235_, v___x_237_, v___x_271_);
lean_inc(v___x_272_);
lean_inc(v___x_208_);
v___x_273_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_272_);
lean_inc(v___x_208_);
v___x_274_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_273_);
lean_inc(v___x_208_);
v___x_275_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_274_);
lean_inc_ref(v___x_234_);
lean_inc(v___x_208_);
v___x_276_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_275_);
v___x_277_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45));
v___x_278_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__46));
lean_inc(v___x_208_);
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_208_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__47));
v___x_281_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48));
lean_inc(v___x_208_);
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_208_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
v___x_283_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50));
v___x_284_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__52));
v___x_285_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__53));
lean_inc(v___x_208_);
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_208_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__55));
v___x_288_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58));
v___x_289_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__59));
lean_inc(v___x_208_);
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_208_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
lean_inc(v___x_208_);
v___x_291_ = l_Lean_Syntax_node1(v___x_208_, v___x_288_, v___x_290_);
v___x_292_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__60));
lean_inc(v___x_208_);
v___x_293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_208_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_inc(v___x_291_);
lean_inc(v___x_208_);
v___x_294_ = l_Lean_Syntax_node3(v___x_208_, v___x_287_, v___x_291_, v___x_293_, v___x_291_);
v___x_295_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__61));
lean_inc(v___x_208_);
v___x_296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_208_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
lean_inc(v___x_208_);
v___x_297_ = l_Lean_Syntax_node3(v___x_208_, v___x_284_, v___x_286_, v___x_294_, v___x_296_);
lean_inc_ref(v___x_220_);
lean_inc(v___x_208_);
v___x_298_ = l_Lean_Syntax_node2(v___x_208_, v___x_283_, v___x_220_, v___x_297_);
lean_inc(v___x_208_);
v___x_299_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_298_);
lean_inc_ref_n(v___x_220_, 2);
lean_inc(v___x_208_);
v___x_300_ = l_Lean_Syntax_node4(v___x_208_, v___x_281_, v___x_282_, v___x_299_, v___x_220_, v___x_220_);
lean_inc(v___x_208_);
v___x_301_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_300_);
lean_inc(v___x_208_);
v___x_302_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_301_);
lean_inc(v___x_208_);
v___x_303_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_302_);
lean_inc(v___x_208_);
v___x_304_ = l_Lean_Syntax_node2(v___x_208_, v___x_277_, v___x_279_, v___x_303_);
v___x_305_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__62));
v___x_306_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63));
lean_inc(v___x_208_);
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_208_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
v___x_308_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65);
v___x_309_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68));
v___x_310_ = l_Lean_addMacroScope(v_quotContext_204_, v___x_309_, v_currMacroScope_205_);
v___x_311_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__70));
lean_inc(v___x_208_);
v___x_312_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_312_, 0, v___x_208_);
lean_ctor_set(v___x_312_, 1, v___x_308_);
lean_ctor_set(v___x_312_, 2, v___x_310_);
lean_ctor_set(v___x_312_, 3, v___x_311_);
lean_inc(v___x_208_);
v___x_313_ = l_Lean_Syntax_node2(v___x_208_, v___x_306_, v___x_307_, v___x_312_);
lean_inc(v___x_208_);
v___x_314_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_313_);
lean_inc(v___x_208_);
v___x_315_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_314_);
lean_inc(v___x_208_);
v___x_316_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_315_);
lean_inc(v___x_208_);
v___x_317_ = l_Lean_Syntax_node2(v___x_208_, v___x_222_, v___x_223_, v___x_316_);
lean_inc_ref_n(v___x_220_, 2);
lean_inc(v___x_208_);
v___x_318_ = l_Lean_Syntax_node5(v___x_208_, v___x_214_, v___x_272_, v___x_220_, v___x_304_, v___x_220_, v___x_317_);
lean_inc(v___x_208_);
v___x_319_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_318_);
lean_inc(v___x_208_);
v___x_320_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_319_);
lean_inc_ref(v___x_234_);
lean_inc(v___x_208_);
v___x_321_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_320_);
v___x_322_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__71));
v___x_323_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72));
lean_inc(v___x_208_);
v___x_324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_208_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
lean_inc(v___x_208_);
v___x_325_ = l_Lean_Syntax_node1(v___x_208_, v___x_323_, v___x_324_);
lean_inc(v___x_208_);
v___x_326_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_325_);
lean_inc(v___x_208_);
v___x_327_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_326_);
lean_inc(v___x_208_);
v___x_328_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_327_);
lean_inc_ref(v___x_237_);
lean_inc(v___x_208_);
v___x_329_ = l_Lean_Syntax_node2(v___x_208_, v___x_235_, v___x_237_, v___x_328_);
v___x_330_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__73));
v___x_331_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74));
lean_inc(v___x_208_);
v___x_332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_208_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_inc(v___x_208_);
v___x_333_ = l_Lean_Syntax_node1(v___x_208_, v___x_331_, v___x_332_);
lean_inc(v___x_208_);
v___x_334_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_333_);
lean_inc(v___x_208_);
v___x_335_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_334_);
lean_inc(v___x_208_);
v___x_336_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_335_);
lean_inc(v___x_208_);
v___x_337_ = l_Lean_Syntax_node2(v___x_208_, v___x_235_, v___x_237_, v___x_336_);
lean_inc_ref(v___x_220_);
lean_inc(v___x_208_);
v___x_338_ = l_Lean_Syntax_node3(v___x_208_, v___x_214_, v___x_329_, v___x_220_, v___x_337_);
lean_inc(v___x_208_);
v___x_339_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_338_);
lean_inc(v___x_208_);
v___x_340_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_339_);
lean_inc_ref(v___x_234_);
lean_inc(v___x_208_);
v___x_341_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_340_);
v___x_342_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__75));
v___x_343_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76));
lean_inc(v___x_208_);
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_208_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
lean_inc(v___x_208_);
v___x_345_ = l_Lean_Syntax_node2(v___x_208_, v___x_343_, v___x_344_, v___x_242_);
lean_inc_ref(v___x_220_);
lean_inc(v___x_218_);
lean_inc(v___x_208_);
v___x_346_ = l_Lean_Syntax_node3(v___x_208_, v___x_214_, v___x_218_, v___x_220_, v___x_345_);
lean_inc(v___x_208_);
v___x_347_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_346_);
lean_inc(v___x_208_);
v___x_348_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_347_);
lean_inc(v___x_208_);
v___x_349_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(12u);
v___x_351_ = lean_mk_empty_array_with_capacity(v___x_350_);
v___x_352_ = lean_array_push(v___x_351_, v___x_218_);
lean_inc_ref(v___x_220_);
v___x_353_ = lean_array_push(v___x_352_, v___x_220_);
v___x_354_ = lean_array_push(v___x_353_, v___x_231_);
lean_inc_ref(v___x_220_);
v___x_355_ = lean_array_push(v___x_354_, v___x_220_);
v___x_356_ = lean_array_push(v___x_355_, v___x_276_);
lean_inc_ref(v___x_220_);
v___x_357_ = lean_array_push(v___x_356_, v___x_220_);
v___x_358_ = lean_array_push(v___x_357_, v___x_321_);
lean_inc_ref(v___x_220_);
v___x_359_ = lean_array_push(v___x_358_, v___x_220_);
v___x_360_ = lean_array_push(v___x_359_, v___x_341_);
lean_inc_ref(v___x_220_);
v___x_361_ = lean_array_push(v___x_360_, v___x_220_);
v___x_362_ = lean_array_push(v___x_361_, v___x_349_);
v___x_363_ = lean_array_push(v___x_362_, v___x_220_);
lean_inc(v___x_208_);
v___x_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_208_);
lean_ctor_set(v___x_364_, 1, v___x_214_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
lean_inc(v___x_208_);
v___x_365_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_364_);
lean_inc(v___x_208_);
v___x_366_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_365_);
v___x_367_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__77));
lean_inc(v___x_208_);
v___x_368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_208_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = l_Lean_Syntax_node3(v___x_208_, v___x_209_, v___x_211_, v___x_366_, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_a_199_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1(lean_object* v_x_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1));
v___x_404_ = l_Lean_Syntax_isOfKind(v_x_400_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_box(1);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
return v___x_406_;
}
else
{
lean_object* v_ref_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_ref_407_ = lean_ctor_get(v_a_401_, 5);
v___x_408_ = 0;
v___x_409_ = l_Lean_SourceInfo_fromRef(v_ref_407_, v___x_408_);
v___x_410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1));
v___x_411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__2));
lean_inc(v___x_409_);
v___x_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_409_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7));
v___x_414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9));
v___x_415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11));
v___x_416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__3));
v___x_417_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4));
lean_inc(v___x_409_);
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_409_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
v___x_419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__5));
lean_inc(v___x_409_);
v___x_420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_409_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5));
v___x_422_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6));
lean_inc(v___x_409_);
v___x_423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_409_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
lean_inc(v___x_409_);
v___x_424_ = l_Lean_Syntax_node1(v___x_409_, v___x_421_, v___x_423_);
lean_inc(v___x_409_);
v___x_425_ = l_Lean_Syntax_node1(v___x_409_, v___x_415_, v___x_424_);
lean_inc(v___x_409_);
v___x_426_ = l_Lean_Syntax_node1(v___x_409_, v___x_414_, v___x_425_);
lean_inc(v___x_409_);
v___x_427_ = l_Lean_Syntax_node1(v___x_409_, v___x_413_, v___x_426_);
lean_inc(v___x_409_);
v___x_428_ = l_Lean_Syntax_node3(v___x_409_, v___x_417_, v___x_418_, v___x_420_, v___x_427_);
lean_inc(v___x_409_);
v___x_429_ = l_Lean_Syntax_node1(v___x_409_, v___x_415_, v___x_428_);
lean_inc(v___x_409_);
v___x_430_ = l_Lean_Syntax_node1(v___x_409_, v___x_414_, v___x_429_);
lean_inc(v___x_409_);
v___x_431_ = l_Lean_Syntax_node1(v___x_409_, v___x_413_, v___x_430_);
v___x_432_ = l_Lean_Syntax_node2(v___x_409_, v___x_410_, v___x_412_, v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_a_402_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___boxed(lean_object* v_x_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1(v_x_434_, v_a_435_, v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL___redArg(lean_object* v_k_438_, lean_object* v_v_439_, lean_object* v_l_440_, lean_object* v_r_441_){
_start:
{
if (lean_obj_tag(v_r_441_) == 0)
{
if (lean_obj_tag(v_l_440_) == 0)
{
lean_object* v_size_442_; lean_object* v_size_443_; lean_object* v_k_444_; lean_object* v_v_445_; lean_object* v_l_446_; lean_object* v_r_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_size_442_ = lean_ctor_get(v_r_441_, 0);
v_size_443_ = lean_ctor_get(v_l_440_, 0);
v_k_444_ = lean_ctor_get(v_l_440_, 1);
v_v_445_ = lean_ctor_get(v_l_440_, 2);
v_l_446_ = lean_ctor_get(v_l_440_, 3);
v_r_447_ = lean_ctor_get(v_l_440_, 4);
lean_inc(v_r_447_);
v___x_448_ = lean_unsigned_to_nat(3u);
v___x_449_ = lean_nat_mul(v___x_448_, v_size_442_);
v___x_450_ = lean_nat_dec_lt(v___x_449_, v_size_443_);
lean_dec(v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_r_447_);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v___x_451_, v_size_443_);
v___x_453_ = lean_nat_add(v___x_452_, v_size_442_);
lean_dec(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_k_438_);
lean_ctor_set(v___x_454_, 2, v_v_439_);
lean_ctor_set(v___x_454_, 3, v_l_440_);
lean_ctor_set(v___x_454_, 4, v_r_441_);
return v___x_454_;
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_520_; 
lean_inc(v_l_446_);
lean_inc(v_v_445_);
lean_inc(v_k_444_);
lean_inc(v_size_443_);
v_isSharedCheck_520_ = !lean_is_exclusive(v_l_440_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; lean_object* v_unused_522_; lean_object* v_unused_523_; lean_object* v_unused_524_; lean_object* v_unused_525_; 
v_unused_521_ = lean_ctor_get(v_l_440_, 4);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_l_440_, 3);
lean_dec(v_unused_522_);
v_unused_523_ = lean_ctor_get(v_l_440_, 2);
lean_dec(v_unused_523_);
v_unused_524_ = lean_ctor_get(v_l_440_, 1);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_l_440_, 0);
lean_dec(v_unused_525_);
v___x_456_ = v_l_440_;
v_isShared_457_ = v_isSharedCheck_520_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_l_440_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_520_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_size_458_; lean_object* v_size_459_; lean_object* v_k_460_; lean_object* v_v_461_; lean_object* v_l_462_; lean_object* v_r_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_size_458_ = lean_ctor_get(v_l_446_, 0);
v_size_459_ = lean_ctor_get(v_r_447_, 0);
v_k_460_ = lean_ctor_get(v_r_447_, 1);
v_v_461_ = lean_ctor_get(v_r_447_, 2);
v_l_462_ = lean_ctor_get(v_r_447_, 3);
v_r_463_ = lean_ctor_get(v_r_447_, 4);
v___x_464_ = lean_unsigned_to_nat(2u);
v___x_465_ = lean_nat_mul(v___x_464_, v_size_458_);
v___x_466_ = lean_nat_dec_lt(v_size_459_, v___x_465_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_494_; 
lean_inc(v_r_463_);
lean_inc(v_l_462_);
lean_inc(v_v_461_);
lean_inc(v_k_460_);
v_isSharedCheck_494_ = !lean_is_exclusive(v_r_447_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_495_ = lean_ctor_get(v_r_447_, 4);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_r_447_, 3);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_r_447_, 2);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_r_447_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_r_447_, 0);
lean_dec(v_unused_499_);
v___x_468_ = v_r_447_;
v_isShared_469_ = v_isSharedCheck_494_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_r_447_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_494_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___x_484_; lean_object* v___y_486_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_add(v___x_470_, v_size_443_);
lean_dec(v_size_443_);
v___x_472_ = lean_nat_add(v___x_471_, v_size_442_);
lean_dec(v___x_471_);
v___x_484_ = lean_nat_add(v___x_470_, v_size_458_);
if (lean_obj_tag(v_l_462_) == 0)
{
lean_object* v_size_492_; 
v_size_492_ = lean_ctor_get(v_l_462_, 0);
lean_inc(v_size_492_);
v___y_486_ = v_size_492_;
goto v___jp_485_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v___y_486_ = v___x_493_;
goto v___jp_485_;
}
v___jp_473_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = lean_nat_add(v___y_474_, v___y_476_);
lean_dec(v___y_476_);
lean_dec(v___y_474_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 4, v_r_441_);
lean_ctor_set(v___x_468_, 3, v_r_463_);
lean_ctor_set(v___x_468_, 2, v_v_439_);
lean_ctor_set(v___x_468_, 1, v_k_438_);
lean_ctor_set(v___x_468_, 0, v___x_477_);
v___x_479_ = v___x_468_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_k_438_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v_r_463_);
lean_ctor_set(v_reuseFailAlloc_483_, 4, v_r_441_);
v___x_479_ = v_reuseFailAlloc_483_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 4, v___x_479_);
lean_ctor_set(v___x_456_, 3, v___y_475_);
lean_ctor_set(v___x_456_, 2, v_v_461_);
lean_ctor_set(v___x_456_, 1, v_k_460_);
lean_ctor_set(v___x_456_, 0, v___x_472_);
v___x_481_ = v___x_456_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_v_461_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v___y_475_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_nat_add(v___x_484_, v___y_486_);
lean_dec(v___y_486_);
lean_dec(v___x_484_);
v___x_488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_k_444_);
lean_ctor_set(v___x_488_, 2, v_v_445_);
lean_ctor_set(v___x_488_, 3, v_l_446_);
lean_ctor_set(v___x_488_, 4, v_l_462_);
v___x_489_ = lean_nat_add(v___x_470_, v_size_442_);
if (lean_obj_tag(v_r_463_) == 0)
{
lean_object* v_size_490_; 
v_size_490_ = lean_ctor_get(v_r_463_, 0);
lean_inc(v_size_490_);
v___y_474_ = v___x_489_;
v___y_475_ = v___x_488_;
v___y_476_ = v_size_490_;
goto v___jp_473_;
}
else
{
lean_object* v___x_491_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___y_474_ = v___x_489_;
v___y_475_ = v___x_488_;
v___y_476_ = v___x_491_;
goto v___jp_473_;
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v___x_500_, v_size_443_);
lean_dec(v_size_443_);
v___x_502_ = lean_nat_add(v___x_501_, v_size_442_);
lean_dec(v___x_501_);
v___x_503_ = lean_nat_add(v___x_500_, v_size_442_);
v___x_504_ = lean_nat_add(v___x_503_, v_size_459_);
lean_dec(v___x_503_);
lean_inc_ref(v_r_441_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 4, v_r_441_);
lean_ctor_set(v___x_456_, 3, v_r_447_);
lean_ctor_set(v___x_456_, 2, v_v_439_);
lean_ctor_set(v___x_456_, 1, v_k_438_);
lean_ctor_set(v___x_456_, 0, v___x_504_);
v___x_506_ = v___x_456_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_k_438_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_r_447_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_r_441_);
v___x_506_ = v_reuseFailAlloc_519_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_isSharedCheck_513_ = !lean_is_exclusive(v_r_441_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; lean_object* v_unused_518_; 
v_unused_514_ = lean_ctor_get(v_r_441_, 4);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_r_441_, 3);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_r_441_, 2);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_r_441_, 1);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_r_441_, 0);
lean_dec(v_unused_518_);
v___x_508_ = v_r_441_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_r_441_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v___x_506_);
lean_ctor_set(v___x_508_, 3, v_l_446_);
lean_ctor_set(v___x_508_, 2, v_v_445_);
lean_ctor_set(v___x_508_, 1, v_k_444_);
lean_ctor_set(v___x_508_, 0, v___x_502_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_k_444_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_v_445_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_l_446_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v___x_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_size_526_ = lean_ctor_get(v_r_441_, 0);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v___x_527_, v_size_526_);
v___x_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_k_438_);
lean_ctor_set(v___x_529_, 2, v_v_439_);
lean_ctor_set(v___x_529_, 3, v_l_440_);
lean_ctor_set(v___x_529_, 4, v_r_441_);
return v___x_529_;
}
}
else
{
if (lean_obj_tag(v_l_440_) == 0)
{
lean_object* v_l_530_; 
v_l_530_ = lean_ctor_get(v_l_440_, 3);
if (lean_obj_tag(v_l_530_) == 0)
{
lean_object* v_r_531_; lean_object* v_k_532_; lean_object* v_v_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_543_; 
lean_inc_ref(v_l_530_);
v_r_531_ = lean_ctor_get(v_l_440_, 4);
v_k_532_ = lean_ctor_get(v_l_440_, 1);
v_v_533_ = lean_ctor_get(v_l_440_, 2);
v_isSharedCheck_543_ = !lean_is_exclusive(v_l_440_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; lean_object* v_unused_545_; 
v_unused_544_ = lean_ctor_get(v_l_440_, 3);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_l_440_, 0);
lean_dec(v_unused_545_);
v___x_535_ = v_l_440_;
v_isShared_536_ = v_isSharedCheck_543_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_r_531_);
lean_inc(v_v_533_);
lean_inc(v_k_532_);
lean_dec(v_l_440_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_543_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_unsigned_to_nat(3u);
v___x_538_ = lean_unsigned_to_nat(1u);
lean_inc(v_r_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 3, v_r_531_);
lean_ctor_set(v___x_535_, 2, v_v_439_);
lean_ctor_set(v___x_535_, 1, v_k_438_);
lean_ctor_set(v___x_535_, 0, v___x_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_k_438_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_r_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_r_531_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_541_, 0, v___x_537_);
lean_ctor_set(v___x_541_, 1, v_k_532_);
lean_ctor_set(v___x_541_, 2, v_v_533_);
lean_ctor_set(v___x_541_, 3, v_l_530_);
lean_ctor_set(v___x_541_, 4, v___x_540_);
return v___x_541_;
}
}
}
else
{
lean_object* v_r_546_; 
v_r_546_ = lean_ctor_get(v_l_440_, 4);
lean_inc(v_r_546_);
if (lean_obj_tag(v_r_546_) == 0)
{
lean_object* v_k_547_; lean_object* v_v_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_l_530_);
v_k_547_ = lean_ctor_get(v_l_440_, 1);
v_v_548_ = lean_ctor_get(v_l_440_, 2);
v_isSharedCheck_570_ = !lean_is_exclusive(v_l_440_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_571_ = lean_ctor_get(v_l_440_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_l_440_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_l_440_, 0);
lean_dec(v_unused_573_);
v___x_550_ = v_l_440_;
v_isShared_551_ = v_isSharedCheck_570_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_v_548_);
lean_inc(v_k_547_);
lean_dec(v_l_440_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_570_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_k_552_; lean_object* v_v_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_566_; 
v_k_552_ = lean_ctor_get(v_r_546_, 1);
v_v_553_ = lean_ctor_get(v_r_546_, 2);
v_isSharedCheck_566_ = !lean_is_exclusive(v_r_546_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_567_ = lean_ctor_get(v_r_546_, 4);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_r_546_, 3);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_r_546_, 0);
lean_dec(v_unused_569_);
v___x_555_ = v_r_546_;
v_isShared_556_ = v_isSharedCheck_566_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_v_553_);
lean_inc(v_k_552_);
lean_dec(v_r_546_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_566_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = lean_unsigned_to_nat(3u);
v___x_558_ = lean_unsigned_to_nat(1u);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 4, v_l_530_);
lean_ctor_set(v___x_555_, 3, v_l_530_);
lean_ctor_set(v___x_555_, 2, v_v_548_);
lean_ctor_set(v___x_555_, 1, v_k_547_);
lean_ctor_set(v___x_555_, 0, v___x_558_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_k_547_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_v_548_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_l_530_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_l_530_);
v___x_560_ = v_reuseFailAlloc_565_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 4, v_l_530_);
lean_ctor_set(v___x_550_, 2, v_v_439_);
lean_ctor_set(v___x_550_, 1, v_k_438_);
lean_ctor_set(v___x_550_, 0, v___x_558_);
v___x_562_ = v___x_550_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_k_438_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_l_530_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_l_530_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_563_, 0, v___x_557_);
lean_ctor_set(v___x_563_, 1, v_k_552_);
lean_ctor_set(v___x_563_, 2, v_v_553_);
lean_ctor_set(v___x_563_, 3, v___x_560_);
lean_ctor_set(v___x_563_, 4, v___x_562_);
return v___x_563_;
}
}
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(2u);
v___x_575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_k_438_);
lean_ctor_set(v___x_575_, 2, v_v_439_);
lean_ctor_set(v___x_575_, 3, v_l_440_);
lean_ctor_set(v___x_575_, 4, v_r_546_);
return v___x_575_;
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_k_438_);
lean_ctor_set(v___x_577_, 2, v_v_439_);
lean_ctor_set(v___x_577_, 3, v_l_440_);
lean_ctor_set(v___x_577_, 4, v_l_440_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_k_580_, lean_object* v_v_581_, lean_object* v_l_582_, lean_object* v_r_583_, lean_object* v_hlb_584_, lean_object* v_hrb_585_, lean_object* v_hlr_586_){
_start:
{
if (lean_obj_tag(v_r_583_) == 0)
{
if (lean_obj_tag(v_l_582_) == 0)
{
lean_object* v_size_587_; lean_object* v_size_588_; lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_l_591_; lean_object* v_r_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_size_587_ = lean_ctor_get(v_r_583_, 0);
v_size_588_ = lean_ctor_get(v_l_582_, 0);
v_k_589_ = lean_ctor_get(v_l_582_, 1);
v_v_590_ = lean_ctor_get(v_l_582_, 2);
v_l_591_ = lean_ctor_get(v_l_582_, 3);
v_r_592_ = lean_ctor_get(v_l_582_, 4);
lean_inc(v_r_592_);
v___x_593_ = lean_unsigned_to_nat(3u);
v___x_594_ = lean_nat_mul(v___x_593_, v_size_587_);
v___x_595_ = lean_nat_dec_lt(v___x_594_, v_size_588_);
lean_dec(v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_r_592_);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v___x_596_, v_size_588_);
v___x_598_ = lean_nat_add(v___x_597_, v_size_587_);
lean_dec(v___x_597_);
v___x_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_k_580_);
lean_ctor_set(v___x_599_, 2, v_v_581_);
lean_ctor_set(v___x_599_, 3, v_l_582_);
lean_ctor_set(v___x_599_, 4, v_r_583_);
return v___x_599_;
}
else
{
lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_665_; 
lean_inc(v_l_591_);
lean_inc(v_v_590_);
lean_inc(v_k_589_);
lean_inc(v_size_588_);
v_isSharedCheck_665_ = !lean_is_exclusive(v_l_582_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; lean_object* v_unused_667_; lean_object* v_unused_668_; lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_666_ = lean_ctor_get(v_l_582_, 4);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_l_582_, 3);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_l_582_, 2);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_l_582_, 1);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_l_582_, 0);
lean_dec(v_unused_670_);
v___x_601_ = v_l_582_;
v_isShared_602_ = v_isSharedCheck_665_;
goto v_resetjp_600_;
}
else
{
lean_dec(v_l_582_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_665_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_size_603_; lean_object* v_size_604_; lean_object* v_k_605_; lean_object* v_v_606_; lean_object* v_l_607_; lean_object* v_r_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_size_603_ = lean_ctor_get(v_l_591_, 0);
v_size_604_ = lean_ctor_get(v_r_592_, 0);
v_k_605_ = lean_ctor_get(v_r_592_, 1);
v_v_606_ = lean_ctor_get(v_r_592_, 2);
v_l_607_ = lean_ctor_get(v_r_592_, 3);
v_r_608_ = lean_ctor_get(v_r_592_, 4);
v___x_609_ = lean_unsigned_to_nat(2u);
v___x_610_ = lean_nat_mul(v___x_609_, v_size_603_);
v___x_611_ = lean_nat_dec_lt(v_size_604_, v___x_610_);
lean_dec(v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_639_; 
lean_inc(v_r_608_);
lean_inc(v_l_607_);
lean_inc(v_v_606_);
lean_inc(v_k_605_);
v_isSharedCheck_639_ = !lean_is_exclusive(v_r_592_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; lean_object* v_unused_641_; lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_640_ = lean_ctor_get(v_r_592_, 4);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_r_592_, 3);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_r_592_, 2);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_r_592_, 1);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_r_592_, 0);
lean_dec(v_unused_644_);
v___x_613_ = v_r_592_;
v_isShared_614_ = v_isSharedCheck_639_;
goto v_resetjp_612_;
}
else
{
lean_dec(v_r_592_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_639_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___x_629_; lean_object* v___y_631_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v___x_615_, v_size_588_);
lean_dec(v_size_588_);
v___x_617_ = lean_nat_add(v___x_616_, v_size_587_);
lean_dec(v___x_616_);
v___x_629_ = lean_nat_add(v___x_615_, v_size_603_);
if (lean_obj_tag(v_l_607_) == 0)
{
lean_object* v_size_637_; 
v_size_637_ = lean_ctor_get(v_l_607_, 0);
lean_inc(v_size_637_);
v___y_631_ = v_size_637_;
goto v___jp_630_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___y_631_ = v___x_638_;
goto v___jp_630_;
}
v___jp_618_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_nat_add(v___y_619_, v___y_621_);
lean_dec(v___y_621_);
lean_dec(v___y_619_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v_r_583_);
lean_ctor_set(v___x_613_, 3, v_r_608_);
lean_ctor_set(v___x_613_, 2, v_v_581_);
lean_ctor_set(v___x_613_, 1, v_k_580_);
lean_ctor_set(v___x_613_, 0, v___x_622_);
v___x_624_ = v___x_613_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v_r_608_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v_r_583_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v___x_624_);
lean_ctor_set(v___x_601_, 3, v___y_620_);
lean_ctor_set(v___x_601_, 2, v_v_606_);
lean_ctor_set(v___x_601_, 1, v_k_605_);
lean_ctor_set(v___x_601_, 0, v___x_617_);
v___x_626_ = v___x_601_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_k_605_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_v_606_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v___y_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
v___jp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_nat_add(v___x_629_, v___y_631_);
lean_dec(v___y_631_);
lean_dec(v___x_629_);
v___x_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_k_589_);
lean_ctor_set(v___x_633_, 2, v_v_590_);
lean_ctor_set(v___x_633_, 3, v_l_591_);
lean_ctor_set(v___x_633_, 4, v_l_607_);
v___x_634_ = lean_nat_add(v___x_615_, v_size_587_);
if (lean_obj_tag(v_r_608_) == 0)
{
lean_object* v_size_635_; 
v_size_635_ = lean_ctor_get(v_r_608_, 0);
lean_inc(v_size_635_);
v___y_619_ = v___x_634_;
v___y_620_ = v___x_633_;
v___y_621_ = v_size_635_;
goto v___jp_618_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___y_619_ = v___x_634_;
v___y_620_ = v___x_633_;
v___y_621_ = v___x_636_;
goto v___jp_618_;
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_add(v___x_645_, v_size_588_);
lean_dec(v_size_588_);
v___x_647_ = lean_nat_add(v___x_646_, v_size_587_);
lean_dec(v___x_646_);
v___x_648_ = lean_nat_add(v___x_645_, v_size_587_);
v___x_649_ = lean_nat_add(v___x_648_, v_size_604_);
lean_dec(v___x_648_);
lean_inc_ref(v_r_583_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_r_583_);
lean_ctor_set(v___x_601_, 3, v_r_592_);
lean_ctor_set(v___x_601_, 2, v_v_581_);
lean_ctor_set(v___x_601_, 1, v_k_580_);
lean_ctor_set(v___x_601_, 0, v___x_649_);
v___x_651_ = v___x_601_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_r_592_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_r_583_);
v___x_651_ = v_reuseFailAlloc_664_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_isSharedCheck_658_ = !lean_is_exclusive(v_r_583_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; lean_object* v_unused_660_; lean_object* v_unused_661_; lean_object* v_unused_662_; lean_object* v_unused_663_; 
v_unused_659_ = lean_ctor_get(v_r_583_, 4);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_r_583_, 3);
lean_dec(v_unused_660_);
v_unused_661_ = lean_ctor_get(v_r_583_, 2);
lean_dec(v_unused_661_);
v_unused_662_ = lean_ctor_get(v_r_583_, 1);
lean_dec(v_unused_662_);
v_unused_663_ = lean_ctor_get(v_r_583_, 0);
lean_dec(v_unused_663_);
v___x_653_ = v_r_583_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_dec(v_r_583_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v___x_651_);
lean_ctor_set(v___x_653_, 3, v_l_591_);
lean_ctor_set(v___x_653_, 2, v_v_590_);
lean_ctor_set(v___x_653_, 1, v_k_589_);
lean_ctor_set(v___x_653_, 0, v___x_647_);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_l_591_);
lean_ctor_set(v_reuseFailAlloc_657_, 4, v___x_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_size_671_ = lean_ctor_get(v_r_583_, 0);
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_add(v___x_672_, v_size_671_);
v___x_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_k_580_);
lean_ctor_set(v___x_674_, 2, v_v_581_);
lean_ctor_set(v___x_674_, 3, v_l_582_);
lean_ctor_set(v___x_674_, 4, v_r_583_);
return v___x_674_;
}
}
else
{
if (lean_obj_tag(v_l_582_) == 0)
{
lean_object* v_l_675_; 
v_l_675_ = lean_ctor_get(v_l_582_, 3);
if (lean_obj_tag(v_l_675_) == 0)
{
lean_object* v_r_676_; lean_object* v_k_677_; lean_object* v_v_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
lean_inc_ref(v_l_675_);
v_r_676_ = lean_ctor_get(v_l_582_, 4);
v_k_677_ = lean_ctor_get(v_l_582_, 1);
v_v_678_ = lean_ctor_get(v_l_582_, 2);
v_isSharedCheck_688_ = !lean_is_exclusive(v_l_582_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_689_ = lean_ctor_get(v_l_582_, 3);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_l_582_, 0);
lean_dec(v_unused_690_);
v___x_680_ = v_l_582_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_r_676_);
lean_inc(v_v_678_);
lean_inc(v_k_677_);
lean_dec(v_l_582_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_682_ = lean_unsigned_to_nat(3u);
v___x_683_ = lean_unsigned_to_nat(1u);
lean_inc(v_r_676_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 3, v_r_676_);
lean_ctor_set(v___x_680_, 2, v_v_581_);
lean_ctor_set(v___x_680_, 1, v_k_580_);
lean_ctor_set(v___x_680_, 0, v___x_683_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_r_676_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_r_676_);
v___x_685_ = v_reuseFailAlloc_687_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; 
v___x_686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_686_, 0, v___x_682_);
lean_ctor_set(v___x_686_, 1, v_k_677_);
lean_ctor_set(v___x_686_, 2, v_v_678_);
lean_ctor_set(v___x_686_, 3, v_l_675_);
lean_ctor_set(v___x_686_, 4, v___x_685_);
return v___x_686_;
}
}
}
else
{
lean_object* v_r_691_; 
v_r_691_ = lean_ctor_get(v_l_582_, 4);
lean_inc(v_r_691_);
if (lean_obj_tag(v_r_691_) == 0)
{
lean_object* v_k_692_; lean_object* v_v_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_715_; 
lean_inc(v_l_675_);
v_k_692_ = lean_ctor_get(v_l_582_, 1);
v_v_693_ = lean_ctor_get(v_l_582_, 2);
v_isSharedCheck_715_ = !lean_is_exclusive(v_l_582_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_716_ = lean_ctor_get(v_l_582_, 4);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_l_582_, 3);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_l_582_, 0);
lean_dec(v_unused_718_);
v___x_695_ = v_l_582_;
v_isShared_696_ = v_isSharedCheck_715_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_v_693_);
lean_inc(v_k_692_);
lean_dec(v_l_582_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_715_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_k_697_; lean_object* v_v_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_711_; 
v_k_697_ = lean_ctor_get(v_r_691_, 1);
v_v_698_ = lean_ctor_get(v_r_691_, 2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_r_691_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_712_ = lean_ctor_get(v_r_691_, 4);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_r_691_, 3);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_r_691_, 0);
lean_dec(v_unused_714_);
v___x_700_ = v_r_691_;
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_v_698_);
lean_inc(v_k_697_);
lean_dec(v_r_691_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = lean_unsigned_to_nat(3u);
v___x_703_ = lean_unsigned_to_nat(1u);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 4, v_l_675_);
lean_ctor_set(v___x_700_, 3, v_l_675_);
lean_ctor_set(v___x_700_, 2, v_v_693_);
lean_ctor_set(v___x_700_, 1, v_k_692_);
lean_ctor_set(v___x_700_, 0, v___x_703_);
v___x_705_ = v___x_700_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_692_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_693_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_l_675_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_l_675_);
v___x_705_ = v_reuseFailAlloc_710_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 4, v_l_675_);
lean_ctor_set(v___x_695_, 2, v_v_581_);
lean_ctor_set(v___x_695_, 1, v_k_580_);
lean_ctor_set(v___x_695_, 0, v___x_703_);
v___x_707_ = v___x_695_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_l_675_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_l_675_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_708_, 0, v___x_702_);
lean_ctor_set(v___x_708_, 1, v_k_697_);
lean_ctor_set(v___x_708_, 2, v_v_698_);
lean_ctor_set(v___x_708_, 3, v___x_705_);
lean_ctor_set(v___x_708_, 4, v___x_707_);
return v___x_708_;
}
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_unsigned_to_nat(2u);
v___x_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v_k_580_);
lean_ctor_set(v___x_720_, 2, v_v_581_);
lean_ctor_set(v___x_720_, 3, v_l_582_);
lean_ctor_set(v___x_720_, 4, v_r_691_);
return v___x_720_;
}
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v_k_580_);
lean_ctor_set(v___x_722_, 2, v_v_581_);
lean_ctor_set(v___x_722_, 3, v_l_582_);
lean_ctor_set(v___x_722_, 4, v_l_582_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase___redArg(lean_object* v_k_723_, lean_object* v_v_724_, lean_object* v_l_725_, lean_object* v_r_726_){
_start:
{
if (lean_obj_tag(v_r_726_) == 0)
{
if (lean_obj_tag(v_l_725_) == 0)
{
lean_object* v_size_727_; lean_object* v_size_728_; lean_object* v_k_729_; lean_object* v_v_730_; lean_object* v_l_731_; lean_object* v_r_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_size_727_ = lean_ctor_get(v_r_726_, 0);
v_size_728_ = lean_ctor_get(v_l_725_, 0);
v_k_729_ = lean_ctor_get(v_l_725_, 1);
v_v_730_ = lean_ctor_get(v_l_725_, 2);
v_l_731_ = lean_ctor_get(v_l_725_, 3);
v_r_732_ = lean_ctor_get(v_l_725_, 4);
lean_inc(v_r_732_);
v___x_733_ = lean_unsigned_to_nat(3u);
v___x_734_ = lean_nat_mul(v___x_733_, v_size_727_);
v___x_735_ = lean_nat_dec_lt(v___x_734_, v_size_728_);
lean_dec(v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_r_732_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v___x_736_, v_size_728_);
v___x_738_ = lean_nat_add(v___x_737_, v_size_727_);
lean_dec(v___x_737_);
v___x_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v_k_723_);
lean_ctor_set(v___x_739_, 2, v_v_724_);
lean_ctor_set(v___x_739_, 3, v_l_725_);
lean_ctor_set(v___x_739_, 4, v_r_726_);
return v___x_739_;
}
else
{
lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_805_; 
lean_inc(v_l_731_);
lean_inc(v_v_730_);
lean_inc(v_k_729_);
lean_inc(v_size_728_);
v_isSharedCheck_805_ = !lean_is_exclusive(v_l_725_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_806_ = lean_ctor_get(v_l_725_, 4);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_l_725_, 3);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_l_725_, 2);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_l_725_, 1);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_l_725_, 0);
lean_dec(v_unused_810_);
v___x_741_ = v_l_725_;
v_isShared_742_ = v_isSharedCheck_805_;
goto v_resetjp_740_;
}
else
{
lean_dec(v_l_725_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_805_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_size_743_; lean_object* v_size_744_; lean_object* v_k_745_; lean_object* v_v_746_; lean_object* v_l_747_; lean_object* v_r_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_size_743_ = lean_ctor_get(v_l_731_, 0);
v_size_744_ = lean_ctor_get(v_r_732_, 0);
v_k_745_ = lean_ctor_get(v_r_732_, 1);
v_v_746_ = lean_ctor_get(v_r_732_, 2);
v_l_747_ = lean_ctor_get(v_r_732_, 3);
v_r_748_ = lean_ctor_get(v_r_732_, 4);
v___x_749_ = lean_unsigned_to_nat(2u);
v___x_750_ = lean_nat_mul(v___x_749_, v_size_743_);
v___x_751_ = lean_nat_dec_lt(v_size_744_, v___x_750_);
lean_dec(v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_779_; 
lean_inc(v_r_748_);
lean_inc(v_l_747_);
lean_inc(v_v_746_);
lean_inc(v_k_745_);
v_isSharedCheck_779_ = !lean_is_exclusive(v_r_732_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_780_ = lean_ctor_get(v_r_732_, 4);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_r_732_, 3);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_r_732_, 2);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_r_732_, 1);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_r_732_, 0);
lean_dec(v_unused_784_);
v___x_753_ = v_r_732_;
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
else
{
lean_dec(v_r_732_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___x_769_; lean_object* v___y_771_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v___x_755_, v_size_728_);
lean_dec(v_size_728_);
v___x_757_ = lean_nat_add(v___x_756_, v_size_727_);
lean_dec(v___x_756_);
v___x_769_ = lean_nat_add(v___x_755_, v_size_743_);
if (lean_obj_tag(v_l_747_) == 0)
{
lean_object* v_size_777_; 
v_size_777_ = lean_ctor_get(v_l_747_, 0);
lean_inc(v_size_777_);
v___y_771_ = v_size_777_;
goto v___jp_770_;
}
else
{
lean_object* v___x_778_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___y_771_ = v___x_778_;
goto v___jp_770_;
}
v___jp_758_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_nat_add(v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec(v___y_760_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 4, v_r_726_);
lean_ctor_set(v___x_753_, 3, v_r_748_);
lean_ctor_set(v___x_753_, 2, v_v_724_);
lean_ctor_set(v___x_753_, 1, v_k_723_);
lean_ctor_set(v___x_753_, 0, v___x_762_);
v___x_764_ = v___x_753_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v_r_748_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v_r_726_);
v___x_764_ = v_reuseFailAlloc_768_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 4, v___x_764_);
lean_ctor_set(v___x_741_, 3, v___y_759_);
lean_ctor_set(v___x_741_, 2, v_v_746_);
lean_ctor_set(v___x_741_, 1, v_k_745_);
lean_ctor_set(v___x_741_, 0, v___x_757_);
v___x_766_ = v___x_741_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_k_745_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_v_746_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v___y_759_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
v___jp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_nat_add(v___x_769_, v___y_771_);
lean_dec(v___y_771_);
lean_dec(v___x_769_);
v___x_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_k_729_);
lean_ctor_set(v___x_773_, 2, v_v_730_);
lean_ctor_set(v___x_773_, 3, v_l_731_);
lean_ctor_set(v___x_773_, 4, v_l_747_);
v___x_774_ = lean_nat_add(v___x_755_, v_size_727_);
if (lean_obj_tag(v_r_748_) == 0)
{
lean_object* v_size_775_; 
v_size_775_ = lean_ctor_get(v_r_748_, 0);
lean_inc(v_size_775_);
v___y_759_ = v___x_773_;
v___y_760_ = v___x_774_;
v___y_761_ = v_size_775_;
goto v___jp_758_;
}
else
{
lean_object* v___x_776_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___y_759_ = v___x_773_;
v___y_760_ = v___x_774_;
v___y_761_ = v___x_776_;
goto v___jp_758_;
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_add(v___x_785_, v_size_728_);
lean_dec(v_size_728_);
v___x_787_ = lean_nat_add(v___x_786_, v_size_727_);
lean_dec(v___x_786_);
v___x_788_ = lean_nat_add(v___x_785_, v_size_727_);
v___x_789_ = lean_nat_add(v___x_788_, v_size_744_);
lean_dec(v___x_788_);
lean_inc_ref(v_r_726_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 4, v_r_726_);
lean_ctor_set(v___x_741_, 3, v_r_732_);
lean_ctor_set(v___x_741_, 2, v_v_724_);
lean_ctor_set(v___x_741_, 1, v_k_723_);
lean_ctor_set(v___x_741_, 0, v___x_789_);
v___x_791_ = v___x_741_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_r_732_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v_r_726_);
v___x_791_ = v_reuseFailAlloc_804_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_isSharedCheck_798_ = !lean_is_exclusive(v_r_726_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_799_ = lean_ctor_get(v_r_726_, 4);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_r_726_, 3);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_r_726_, 2);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_r_726_, 1);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_r_726_, 0);
lean_dec(v_unused_803_);
v___x_793_ = v_r_726_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_r_726_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 4, v___x_791_);
lean_ctor_set(v___x_793_, 3, v_l_731_);
lean_ctor_set(v___x_793_, 2, v_v_730_);
lean_ctor_set(v___x_793_, 1, v_k_729_);
lean_ctor_set(v___x_793_, 0, v___x_787_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_k_729_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_v_730_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_l_731_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v___x_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_size_811_ = lean_ctor_get(v_r_726_, 0);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_nat_add(v___x_812_, v_size_811_);
v___x_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_k_723_);
lean_ctor_set(v___x_814_, 2, v_v_724_);
lean_ctor_set(v___x_814_, 3, v_l_725_);
lean_ctor_set(v___x_814_, 4, v_r_726_);
return v___x_814_;
}
}
else
{
if (lean_obj_tag(v_l_725_) == 0)
{
lean_object* v_l_815_; 
v_l_815_ = lean_ctor_get(v_l_725_, 3);
if (lean_obj_tag(v_l_815_) == 0)
{
lean_object* v_r_816_; 
lean_inc_ref(v_l_815_);
v_r_816_ = lean_ctor_get(v_l_725_, 4);
lean_inc(v_r_816_);
if (lean_obj_tag(v_r_816_) == 0)
{
lean_object* v_size_817_; lean_object* v_k_818_; lean_object* v_v_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_842_; 
v_size_817_ = lean_ctor_get(v_l_725_, 0);
v_k_818_ = lean_ctor_get(v_l_725_, 1);
v_v_819_ = lean_ctor_get(v_l_725_, 2);
v_isSharedCheck_842_ = !lean_is_exclusive(v_l_725_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_843_ = lean_ctor_get(v_l_725_, 4);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_l_725_, 3);
lean_dec(v_unused_844_);
v___x_821_ = v_l_725_;
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_v_819_);
lean_inc(v_k_818_);
lean_inc(v_size_817_);
lean_dec(v_l_725_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_size_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v_size_823_ = lean_ctor_get(v_r_816_, 0);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v___x_824_, v_size_817_);
lean_dec(v_size_817_);
v___x_826_ = lean_nat_add(v___x_824_, v_size_823_);
lean_inc_ref(v_r_816_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 4, v_r_726_);
lean_ctor_set(v___x_821_, 3, v_r_816_);
lean_ctor_set(v___x_821_, 2, v_v_724_);
lean_ctor_set(v___x_821_, 1, v_k_723_);
lean_ctor_set(v___x_821_, 0, v___x_826_);
v___x_828_ = v___x_821_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_r_816_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_r_726_);
v___x_828_ = v_reuseFailAlloc_841_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_isSharedCheck_835_ = !lean_is_exclusive(v_r_816_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_836_ = lean_ctor_get(v_r_816_, 4);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_r_816_, 3);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_r_816_, 2);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_r_816_, 1);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_r_816_, 0);
lean_dec(v_unused_840_);
v___x_830_ = v_r_816_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_dec(v_r_816_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 4, v___x_828_);
lean_ctor_set(v___x_830_, 3, v_l_815_);
lean_ctor_set(v___x_830_, 2, v_v_819_);
lean_ctor_set(v___x_830_, 1, v_k_818_);
lean_ctor_set(v___x_830_, 0, v___x_825_);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_k_818_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_v_819_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_l_815_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v___x_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
else
{
lean_object* v_k_845_; lean_object* v_v_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_856_; 
v_k_845_ = lean_ctor_get(v_l_725_, 1);
v_v_846_ = lean_ctor_get(v_l_725_, 2);
v_isSharedCheck_856_ = !lean_is_exclusive(v_l_725_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_857_ = lean_ctor_get(v_l_725_, 4);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_l_725_, 3);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_l_725_, 0);
lean_dec(v_unused_859_);
v___x_848_ = v_l_725_;
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_v_846_);
lean_inc(v_k_845_);
lean_dec(v_l_725_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_unsigned_to_nat(3u);
v___x_851_ = lean_unsigned_to_nat(1u);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 3, v_r_816_);
lean_ctor_set(v___x_848_, 2, v_v_724_);
lean_ctor_set(v___x_848_, 1, v_k_723_);
lean_ctor_set(v___x_848_, 0, v___x_851_);
v___x_853_ = v___x_848_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_r_816_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_r_816_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_854_, 0, v___x_850_);
lean_ctor_set(v___x_854_, 1, v_k_845_);
lean_ctor_set(v___x_854_, 2, v_v_846_);
lean_ctor_set(v___x_854_, 3, v_l_815_);
lean_ctor_set(v___x_854_, 4, v___x_853_);
return v___x_854_;
}
}
}
}
else
{
lean_object* v_r_860_; 
v_r_860_ = lean_ctor_get(v_l_725_, 4);
lean_inc(v_r_860_);
if (lean_obj_tag(v_r_860_) == 0)
{
lean_object* v_k_861_; lean_object* v_v_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_884_; 
lean_inc(v_l_815_);
v_k_861_ = lean_ctor_get(v_l_725_, 1);
v_v_862_ = lean_ctor_get(v_l_725_, 2);
v_isSharedCheck_884_ = !lean_is_exclusive(v_l_725_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_885_ = lean_ctor_get(v_l_725_, 4);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_l_725_, 3);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_l_725_, 0);
lean_dec(v_unused_887_);
v___x_864_ = v_l_725_;
v_isShared_865_ = v_isSharedCheck_884_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_v_862_);
lean_inc(v_k_861_);
lean_dec(v_l_725_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_884_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_k_866_; lean_object* v_v_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_880_; 
v_k_866_ = lean_ctor_get(v_r_860_, 1);
v_v_867_ = lean_ctor_get(v_r_860_, 2);
v_isSharedCheck_880_ = !lean_is_exclusive(v_r_860_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_881_ = lean_ctor_get(v_r_860_, 4);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_r_860_, 3);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_r_860_, 0);
lean_dec(v_unused_883_);
v___x_869_ = v_r_860_;
v_isShared_870_ = v_isSharedCheck_880_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_v_867_);
lean_inc(v_k_866_);
lean_dec(v_r_860_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_880_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_871_ = lean_unsigned_to_nat(3u);
v___x_872_ = lean_unsigned_to_nat(1u);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 4, v_l_815_);
lean_ctor_set(v___x_869_, 3, v_l_815_);
lean_ctor_set(v___x_869_, 2, v_v_862_);
lean_ctor_set(v___x_869_, 1, v_k_861_);
lean_ctor_set(v___x_869_, 0, v___x_872_);
v___x_874_ = v___x_869_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_l_815_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_l_815_);
v___x_874_ = v_reuseFailAlloc_879_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v_l_815_);
lean_ctor_set(v___x_864_, 2, v_v_724_);
lean_ctor_set(v___x_864_, 1, v_k_723_);
lean_ctor_set(v___x_864_, 0, v___x_872_);
v___x_876_ = v___x_864_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_l_815_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_l_815_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_877_, 0, v___x_871_);
lean_ctor_set(v___x_877_, 1, v_k_866_);
lean_ctor_set(v___x_877_, 2, v_v_867_);
lean_ctor_set(v___x_877_, 3, v___x_874_);
lean_ctor_set(v___x_877_, 4, v___x_876_);
return v___x_877_;
}
}
}
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(2u);
v___x_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v_k_723_);
lean_ctor_set(v___x_889_, 2, v_v_724_);
lean_ctor_set(v___x_889_, 3, v_l_725_);
lean_ctor_set(v___x_889_, 4, v_r_860_);
return v___x_889_;
}
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_k_723_);
lean_ctor_set(v___x_891_, 2, v_v_724_);
lean_ctor_set(v___x_891_, 3, v_l_725_);
lean_ctor_set(v___x_891_, 4, v_l_725_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase(lean_object* v_00_u03b1_892_, lean_object* v_00_u03b2_893_, lean_object* v_k_894_, lean_object* v_v_895_, lean_object* v_l_896_, lean_object* v_r_897_, lean_object* v_hlb_898_, lean_object* v_hrb_899_, lean_object* v_hlr_900_){
_start:
{
if (lean_obj_tag(v_r_897_) == 0)
{
if (lean_obj_tag(v_l_896_) == 0)
{
lean_object* v_size_901_; lean_object* v_size_902_; lean_object* v_k_903_; lean_object* v_v_904_; lean_object* v_l_905_; lean_object* v_r_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_size_901_ = lean_ctor_get(v_r_897_, 0);
v_size_902_ = lean_ctor_get(v_l_896_, 0);
v_k_903_ = lean_ctor_get(v_l_896_, 1);
v_v_904_ = lean_ctor_get(v_l_896_, 2);
v_l_905_ = lean_ctor_get(v_l_896_, 3);
v_r_906_ = lean_ctor_get(v_l_896_, 4);
lean_inc(v_r_906_);
v___x_907_ = lean_unsigned_to_nat(3u);
v___x_908_ = lean_nat_mul(v___x_907_, v_size_901_);
v___x_909_ = lean_nat_dec_lt(v___x_908_, v_size_902_);
lean_dec(v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v_r_906_);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_add(v___x_910_, v_size_902_);
v___x_912_ = lean_nat_add(v___x_911_, v_size_901_);
lean_dec(v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v_k_894_);
lean_ctor_set(v___x_913_, 2, v_v_895_);
lean_ctor_set(v___x_913_, 3, v_l_896_);
lean_ctor_set(v___x_913_, 4, v_r_897_);
return v___x_913_;
}
else
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_979_; 
lean_inc(v_l_905_);
lean_inc(v_v_904_);
lean_inc(v_k_903_);
lean_inc(v_size_902_);
v_isSharedCheck_979_ = !lean_is_exclusive(v_l_896_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; lean_object* v_unused_984_; 
v_unused_980_ = lean_ctor_get(v_l_896_, 4);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_896_, 3);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_l_896_, 2);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_l_896_, 1);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_l_896_, 0);
lean_dec(v_unused_984_);
v___x_915_ = v_l_896_;
v_isShared_916_ = v_isSharedCheck_979_;
goto v_resetjp_914_;
}
else
{
lean_dec(v_l_896_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_979_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_size_917_; lean_object* v_size_918_; lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v_l_921_; lean_object* v_r_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_size_917_ = lean_ctor_get(v_l_905_, 0);
v_size_918_ = lean_ctor_get(v_r_906_, 0);
v_k_919_ = lean_ctor_get(v_r_906_, 1);
v_v_920_ = lean_ctor_get(v_r_906_, 2);
v_l_921_ = lean_ctor_get(v_r_906_, 3);
v_r_922_ = lean_ctor_get(v_r_906_, 4);
v___x_923_ = lean_unsigned_to_nat(2u);
v___x_924_ = lean_nat_mul(v___x_923_, v_size_917_);
v___x_925_ = lean_nat_dec_lt(v_size_918_, v___x_924_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_953_; 
lean_inc(v_r_922_);
lean_inc(v_l_921_);
lean_inc(v_v_920_);
lean_inc(v_k_919_);
v_isSharedCheck_953_ = !lean_is_exclusive(v_r_906_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; 
v_unused_954_ = lean_ctor_get(v_r_906_, 4);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_r_906_, 3);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_r_906_, 2);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_r_906_, 1);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_r_906_, 0);
lean_dec(v_unused_958_);
v___x_927_ = v_r_906_;
v_isShared_928_ = v_isSharedCheck_953_;
goto v_resetjp_926_;
}
else
{
lean_dec(v_r_906_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_953_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___x_943_; lean_object* v___y_945_; 
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v___x_929_, v_size_902_);
lean_dec(v_size_902_);
v___x_931_ = lean_nat_add(v___x_930_, v_size_901_);
lean_dec(v___x_930_);
v___x_943_ = lean_nat_add(v___x_929_, v_size_917_);
if (lean_obj_tag(v_l_921_) == 0)
{
lean_object* v_size_951_; 
v_size_951_ = lean_ctor_get(v_l_921_, 0);
lean_inc(v_size_951_);
v___y_945_ = v_size_951_;
goto v___jp_944_;
}
else
{
lean_object* v___x_952_; 
v___x_952_ = lean_unsigned_to_nat(0u);
v___y_945_ = v___x_952_;
goto v___jp_944_;
}
v___jp_932_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_nat_add(v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 4, v_r_897_);
lean_ctor_set(v___x_927_, 3, v_r_922_);
lean_ctor_set(v___x_927_, 2, v_v_895_);
lean_ctor_set(v___x_927_, 1, v_k_894_);
lean_ctor_set(v___x_927_, 0, v___x_936_);
v___x_938_ = v___x_927_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_r_922_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_r_897_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 4, v___x_938_);
lean_ctor_set(v___x_915_, 3, v___y_933_);
lean_ctor_set(v___x_915_, 2, v_v_920_);
lean_ctor_set(v___x_915_, 1, v_k_919_);
lean_ctor_set(v___x_915_, 0, v___x_931_);
v___x_940_ = v___x_915_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v___y_933_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
v___jp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_nat_add(v___x_943_, v___y_945_);
lean_dec(v___y_945_);
lean_dec(v___x_943_);
v___x_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_k_903_);
lean_ctor_set(v___x_947_, 2, v_v_904_);
lean_ctor_set(v___x_947_, 3, v_l_905_);
lean_ctor_set(v___x_947_, 4, v_l_921_);
v___x_948_ = lean_nat_add(v___x_929_, v_size_901_);
if (lean_obj_tag(v_r_922_) == 0)
{
lean_object* v_size_949_; 
v_size_949_ = lean_ctor_get(v_r_922_, 0);
lean_inc(v_size_949_);
v___y_933_ = v___x_947_;
v___y_934_ = v___x_948_;
v___y_935_ = v_size_949_;
goto v___jp_932_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___y_933_ = v___x_947_;
v___y_934_ = v___x_948_;
v___y_935_ = v___x_950_;
goto v___jp_932_;
}
}
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_add(v___x_959_, v_size_902_);
lean_dec(v_size_902_);
v___x_961_ = lean_nat_add(v___x_960_, v_size_901_);
lean_dec(v___x_960_);
v___x_962_ = lean_nat_add(v___x_959_, v_size_901_);
v___x_963_ = lean_nat_add(v___x_962_, v_size_918_);
lean_dec(v___x_962_);
lean_inc_ref(v_r_897_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 4, v_r_897_);
lean_ctor_set(v___x_915_, 3, v_r_906_);
lean_ctor_set(v___x_915_, 2, v_v_895_);
lean_ctor_set(v___x_915_, 1, v_k_894_);
lean_ctor_set(v___x_915_, 0, v___x_963_);
v___x_965_ = v___x_915_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_r_906_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_r_897_);
v___x_965_ = v_reuseFailAlloc_978_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_isSharedCheck_972_ = !lean_is_exclusive(v_r_897_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; lean_object* v_unused_976_; lean_object* v_unused_977_; 
v_unused_973_ = lean_ctor_get(v_r_897_, 4);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_r_897_, 3);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_r_897_, 2);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_r_897_, 1);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_r_897_, 0);
lean_dec(v_unused_977_);
v___x_967_ = v_r_897_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_dec(v_r_897_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v___x_965_);
lean_ctor_set(v___x_967_, 3, v_l_905_);
lean_ctor_set(v___x_967_, 2, v_v_904_);
lean_ctor_set(v___x_967_, 1, v_k_903_);
lean_ctor_set(v___x_967_, 0, v___x_961_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_k_903_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_v_904_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_l_905_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v___x_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_size_985_ = lean_ctor_get(v_r_897_, 0);
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_nat_add(v___x_986_, v_size_985_);
v___x_988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v_k_894_);
lean_ctor_set(v___x_988_, 2, v_v_895_);
lean_ctor_set(v___x_988_, 3, v_l_896_);
lean_ctor_set(v___x_988_, 4, v_r_897_);
return v___x_988_;
}
}
else
{
if (lean_obj_tag(v_l_896_) == 0)
{
lean_object* v_l_989_; 
v_l_989_ = lean_ctor_get(v_l_896_, 3);
if (lean_obj_tag(v_l_989_) == 0)
{
lean_object* v_r_990_; 
lean_inc_ref(v_l_989_);
v_r_990_ = lean_ctor_get(v_l_896_, 4);
lean_inc(v_r_990_);
if (lean_obj_tag(v_r_990_) == 0)
{
lean_object* v_size_991_; lean_object* v_k_992_; lean_object* v_v_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1016_; 
v_size_991_ = lean_ctor_get(v_l_896_, 0);
v_k_992_ = lean_ctor_get(v_l_896_, 1);
v_v_993_ = lean_ctor_get(v_l_896_, 2);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_l_896_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1017_ = lean_ctor_get(v_l_896_, 4);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_l_896_, 3);
lean_dec(v_unused_1018_);
v___x_995_ = v_l_896_;
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_v_993_);
lean_inc(v_k_992_);
lean_inc(v_size_991_);
lean_dec(v_l_896_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_size_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_size_997_ = lean_ctor_get(v_r_990_, 0);
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_nat_add(v___x_998_, v_size_991_);
lean_dec(v_size_991_);
v___x_1000_ = lean_nat_add(v___x_998_, v_size_997_);
lean_inc_ref(v_r_990_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v_r_897_);
lean_ctor_set(v___x_995_, 3, v_r_990_);
lean_ctor_set(v___x_995_, 2, v_v_895_);
lean_ctor_set(v___x_995_, 1, v_k_894_);
lean_ctor_set(v___x_995_, 0, v___x_1000_);
v___x_1002_ = v___x_995_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v_r_990_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_r_897_);
v___x_1002_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_isSharedCheck_1009_ = !lean_is_exclusive(v_r_990_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; lean_object* v_unused_1011_; lean_object* v_unused_1012_; lean_object* v_unused_1013_; lean_object* v_unused_1014_; 
v_unused_1010_ = lean_ctor_get(v_r_990_, 4);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_r_990_, 3);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_r_990_, 2);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_r_990_, 1);
lean_dec(v_unused_1013_);
v_unused_1014_ = lean_ctor_get(v_r_990_, 0);
lean_dec(v_unused_1014_);
v___x_1004_ = v_r_990_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v_r_990_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 4, v___x_1002_);
lean_ctor_set(v___x_1004_, 3, v_l_989_);
lean_ctor_set(v___x_1004_, 2, v_v_993_);
lean_ctor_set(v___x_1004_, 1, v_k_992_);
lean_ctor_set(v___x_1004_, 0, v___x_999_);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_k_992_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_v_993_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_l_989_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v___x_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
else
{
lean_object* v_k_1019_; lean_object* v_v_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1030_; 
v_k_1019_ = lean_ctor_get(v_l_896_, 1);
v_v_1020_ = lean_ctor_get(v_l_896_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_l_896_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; 
v_unused_1031_ = lean_ctor_get(v_l_896_, 4);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_l_896_, 3);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_l_896_, 0);
lean_dec(v_unused_1033_);
v___x_1022_ = v_l_896_;
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_v_1020_);
lean_inc(v_k_1019_);
lean_dec(v_l_896_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1024_ = lean_unsigned_to_nat(3u);
v___x_1025_ = lean_unsigned_to_nat(1u);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 3, v_r_990_);
lean_ctor_set(v___x_1022_, 2, v_v_895_);
lean_ctor_set(v___x_1022_, 1, v_k_894_);
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1027_ = v___x_1022_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_r_990_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_r_990_);
v___x_1027_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v_k_1019_);
lean_ctor_set(v___x_1028_, 2, v_v_1020_);
lean_ctor_set(v___x_1028_, 3, v_l_989_);
lean_ctor_set(v___x_1028_, 4, v___x_1027_);
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_r_1034_; 
v_r_1034_ = lean_ctor_get(v_l_896_, 4);
lean_inc(v_r_1034_);
if (lean_obj_tag(v_r_1034_) == 0)
{
lean_object* v_k_1035_; lean_object* v_v_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1058_; 
lean_inc(v_l_989_);
v_k_1035_ = lean_ctor_get(v_l_896_, 1);
v_v_1036_ = lean_ctor_get(v_l_896_, 2);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_l_896_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; 
v_unused_1059_ = lean_ctor_get(v_l_896_, 4);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_l_896_, 3);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_l_896_, 0);
lean_dec(v_unused_1061_);
v___x_1038_ = v_l_896_;
v_isShared_1039_ = v_isSharedCheck_1058_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_v_1036_);
lean_inc(v_k_1035_);
lean_dec(v_l_896_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1058_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_k_1040_; lean_object* v_v_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1054_; 
v_k_1040_ = lean_ctor_get(v_r_1034_, 1);
v_v_1041_ = lean_ctor_get(v_r_1034_, 2);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; lean_object* v_unused_1056_; lean_object* v_unused_1057_; 
v_unused_1055_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1055_);
v_unused_1056_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1056_);
v_unused_1057_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1057_);
v___x_1043_ = v_r_1034_;
v_isShared_1044_ = v_isSharedCheck_1054_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_v_1041_);
lean_inc(v_k_1040_);
lean_dec(v_r_1034_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1054_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = lean_unsigned_to_nat(3u);
v___x_1046_ = lean_unsigned_to_nat(1u);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 4, v_l_989_);
lean_ctor_set(v___x_1043_, 3, v_l_989_);
lean_ctor_set(v___x_1043_, 2, v_v_1036_);
lean_ctor_set(v___x_1043_, 1, v_k_1035_);
lean_ctor_set(v___x_1043_, 0, v___x_1046_);
v___x_1048_ = v___x_1043_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_1035_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_1036_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_l_989_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_l_989_);
v___x_1048_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 4, v_l_989_);
lean_ctor_set(v___x_1038_, 2, v_v_895_);
lean_ctor_set(v___x_1038_, 1, v_k_894_);
lean_ctor_set(v___x_1038_, 0, v___x_1046_);
v___x_1050_ = v___x_1038_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_l_989_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_l_989_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1045_);
lean_ctor_set(v___x_1051_, 1, v_k_1040_);
lean_ctor_set(v___x_1051_, 2, v_v_1041_);
lean_ctor_set(v___x_1051_, 3, v___x_1048_);
lean_ctor_set(v___x_1051_, 4, v___x_1050_);
return v___x_1051_;
}
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(2u);
v___x_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_k_894_);
lean_ctor_set(v___x_1063_, 2, v_v_895_);
lean_ctor_set(v___x_1063_, 3, v_l_896_);
lean_ctor_set(v___x_1063_, 4, v_r_1034_);
return v___x_1063_;
}
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_k_894_);
lean_ctor_set(v___x_1065_, 2, v_v_895_);
lean_ctor_set(v___x_1065_, 3, v_l_896_);
lean_ctor_set(v___x_1065_, 4, v_l_896_);
return v___x_1065_;
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1069_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2));
v___x_1070_ = lean_unsigned_to_nat(35u);
v___x_1071_ = lean_unsigned_to_nat(182u);
v___x_1072_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1));
v___x_1073_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_1074_ = l_mkPanicMessageWithDecl(v___x_1073_, v___x_1072_, v___x_1071_, v___x_1070_, v___x_1069_);
return v___x_1074_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1075_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2));
v___x_1076_ = lean_unsigned_to_nat(21u);
v___x_1077_ = lean_unsigned_to_nat(183u);
v___x_1078_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1));
v___x_1079_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_1080_ = l_mkPanicMessageWithDecl(v___x_1079_, v___x_1078_, v___x_1077_, v___x_1076_, v___x_1075_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg(lean_object* v_k_1081_, lean_object* v_v_1082_, lean_object* v_l_1083_, lean_object* v_r_1084_){
_start:
{
if (lean_obj_tag(v_r_1084_) == 0)
{
if (lean_obj_tag(v_l_1083_) == 0)
{
lean_object* v_size_1085_; lean_object* v_size_1086_; lean_object* v_k_1087_; lean_object* v_v_1088_; lean_object* v_l_1089_; lean_object* v_r_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_size_1085_ = lean_ctor_get(v_r_1084_, 0);
v_size_1086_ = lean_ctor_get(v_l_1083_, 0);
v_k_1087_ = lean_ctor_get(v_l_1083_, 1);
v_v_1088_ = lean_ctor_get(v_l_1083_, 2);
v_l_1089_ = lean_ctor_get(v_l_1083_, 3);
v_r_1090_ = lean_ctor_get(v_l_1083_, 4);
lean_inc(v_r_1090_);
v___x_1091_ = lean_unsigned_to_nat(3u);
v___x_1092_ = lean_nat_mul(v___x_1091_, v_size_1085_);
v___x_1093_ = lean_nat_dec_lt(v___x_1092_, v_size_1086_);
lean_dec(v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_r_1090_);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_add(v___x_1094_, v_size_1086_);
v___x_1096_ = lean_nat_add(v___x_1095_, v_size_1085_);
lean_dec(v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v_k_1081_);
lean_ctor_set(v___x_1097_, 2, v_v_1082_);
lean_ctor_set(v___x_1097_, 3, v_l_1083_);
lean_ctor_set(v___x_1097_, 4, v_r_1084_);
return v___x_1097_;
}
else
{
lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1169_; 
lean_inc(v_l_1089_);
lean_inc(v_v_1088_);
lean_inc(v_k_1087_);
lean_inc(v_size_1086_);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_l_1083_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; 
v_unused_1170_ = lean_ctor_get(v_l_1083_, 4);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_l_1083_, 3);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_l_1083_, 2);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_l_1083_, 1);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_l_1083_, 0);
lean_dec(v_unused_1174_);
v___x_1099_ = v_l_1083_;
v_isShared_1100_ = v_isSharedCheck_1169_;
goto v_resetjp_1098_;
}
else
{
lean_dec(v_l_1083_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1169_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
if (lean_obj_tag(v_l_1089_) == 0)
{
if (lean_obj_tag(v_r_1090_) == 0)
{
lean_object* v_size_1101_; lean_object* v_size_1102_; lean_object* v_k_1103_; lean_object* v_v_1104_; lean_object* v_l_1105_; lean_object* v_r_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_size_1101_ = lean_ctor_get(v_l_1089_, 0);
v_size_1102_ = lean_ctor_get(v_r_1090_, 0);
v_k_1103_ = lean_ctor_get(v_r_1090_, 1);
v_v_1104_ = lean_ctor_get(v_r_1090_, 2);
v_l_1105_ = lean_ctor_get(v_r_1090_, 3);
v_r_1106_ = lean_ctor_get(v_r_1090_, 4);
v___x_1107_ = lean_unsigned_to_nat(2u);
v___x_1108_ = lean_nat_mul(v___x_1107_, v_size_1101_);
v___x_1109_ = lean_nat_dec_lt(v_size_1102_, v___x_1108_);
lean_dec(v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1137_; 
lean_inc(v_r_1106_);
lean_inc(v_l_1105_);
lean_inc(v_v_1104_);
lean_inc(v_k_1103_);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_r_1090_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; lean_object* v_unused_1141_; lean_object* v_unused_1142_; 
v_unused_1138_ = lean_ctor_get(v_r_1090_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_r_1090_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_r_1090_, 2);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_r_1090_, 1);
lean_dec(v_unused_1141_);
v_unused_1142_ = lean_ctor_get(v_r_1090_, 0);
lean_dec(v_unused_1142_);
v___x_1111_ = v_r_1090_;
v_isShared_1112_ = v_isSharedCheck_1137_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v_r_1090_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1137_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___x_1127_; lean_object* v___y_1129_; 
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v___x_1113_, v_size_1086_);
lean_dec(v_size_1086_);
v___x_1115_ = lean_nat_add(v___x_1114_, v_size_1085_);
lean_dec(v___x_1114_);
v___x_1127_ = lean_nat_add(v___x_1113_, v_size_1101_);
if (lean_obj_tag(v_l_1105_) == 0)
{
lean_object* v_size_1135_; 
v_size_1135_ = lean_ctor_get(v_l_1105_, 0);
lean_inc(v_size_1135_);
v___y_1129_ = v_size_1135_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_unsigned_to_nat(0u);
v___y_1129_ = v___x_1136_;
goto v___jp_1128_;
}
v___jp_1116_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = lean_nat_add(v___y_1117_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec(v___y_1117_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 4, v_r_1084_);
lean_ctor_set(v___x_1111_, 3, v_r_1106_);
lean_ctor_set(v___x_1111_, 2, v_v_1082_);
lean_ctor_set(v___x_1111_, 1, v_k_1081_);
lean_ctor_set(v___x_1111_, 0, v___x_1120_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_r_1106_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_r_1084_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 4, v___x_1122_);
lean_ctor_set(v___x_1099_, 3, v___y_1118_);
lean_ctor_set(v___x_1099_, 2, v_v_1104_);
lean_ctor_set(v___x_1099_, 1, v_k_1103_);
lean_ctor_set(v___x_1099_, 0, v___x_1115_);
v___x_1124_ = v___x_1099_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v___y_1118_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_nat_add(v___x_1127_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec(v___x_1127_);
v___x_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v_k_1087_);
lean_ctor_set(v___x_1131_, 2, v_v_1088_);
lean_ctor_set(v___x_1131_, 3, v_l_1089_);
lean_ctor_set(v___x_1131_, 4, v_l_1105_);
v___x_1132_ = lean_nat_add(v___x_1113_, v_size_1085_);
if (lean_obj_tag(v_r_1106_) == 0)
{
lean_object* v_size_1133_; 
v_size_1133_ = lean_ctor_get(v_r_1106_, 0);
lean_inc(v_size_1133_);
v___y_1117_ = v___x_1132_;
v___y_1118_ = v___x_1131_;
v___y_1119_ = v_size_1133_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___y_1117_ = v___x_1132_;
v___y_1118_ = v___x_1131_;
v___y_1119_ = v___x_1134_;
goto v___jp_1116_;
}
}
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = lean_nat_add(v___x_1143_, v_size_1086_);
lean_dec(v_size_1086_);
v___x_1145_ = lean_nat_add(v___x_1144_, v_size_1085_);
lean_dec(v___x_1144_);
v___x_1146_ = lean_nat_add(v___x_1143_, v_size_1085_);
v___x_1147_ = lean_nat_add(v___x_1146_, v_size_1102_);
lean_dec(v___x_1146_);
lean_inc_ref(v_r_1084_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 4, v_r_1084_);
lean_ctor_set(v___x_1099_, 3, v_r_1090_);
lean_ctor_set(v___x_1099_, 2, v_v_1082_);
lean_ctor_set(v___x_1099_, 1, v_k_1081_);
lean_ctor_set(v___x_1099_, 0, v___x_1147_);
v___x_1149_ = v___x_1099_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_r_1090_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_r_1084_);
v___x_1149_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_isSharedCheck_1156_ = !lean_is_exclusive(v_r_1084_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; lean_object* v_unused_1158_; lean_object* v_unused_1159_; lean_object* v_unused_1160_; lean_object* v_unused_1161_; 
v_unused_1157_ = lean_ctor_get(v_r_1084_, 4);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_r_1084_, 3);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_r_1084_, 2);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_r_1084_, 1);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_r_1084_, 0);
lean_dec(v_unused_1161_);
v___x_1151_ = v_r_1084_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v_r_1084_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 4, v___x_1149_);
lean_ctor_set(v___x_1151_, 3, v_l_1089_);
lean_ctor_set(v___x_1151_, 2, v_v_1088_);
lean_ctor_set(v___x_1151_, 1, v_k_1087_);
lean_ctor_set(v___x_1151_, 0, v___x_1145_);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_l_1089_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v___x_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref(v_l_1089_);
lean_del_object(v___x_1099_);
lean_dec(v_v_1088_);
lean_dec(v_k_1087_);
lean_dec(v_size_1086_);
lean_dec_ref(v_r_1084_);
lean_dec(v_v_1082_);
lean_dec(v_k_1081_);
v___x_1163_ = lean_box(1);
v___x_1164_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
v___x_1165_ = l_panic___redArg(v___x_1163_, v___x_1164_);
return v___x_1165_;
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_del_object(v___x_1099_);
lean_dec(v_r_1090_);
lean_dec(v_v_1088_);
lean_dec(v_k_1087_);
lean_dec(v_size_1086_);
lean_dec_ref(v_r_1084_);
lean_dec(v_v_1082_);
lean_dec(v_k_1081_);
v___x_1166_ = lean_box(1);
v___x_1167_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
v___x_1168_ = l_panic___redArg(v___x_1166_, v___x_1167_);
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_size_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_size_1175_ = lean_ctor_get(v_r_1084_, 0);
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_nat_add(v___x_1176_, v_size_1175_);
v___x_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_k_1081_);
lean_ctor_set(v___x_1178_, 2, v_v_1082_);
lean_ctor_set(v___x_1178_, 3, v_l_1083_);
lean_ctor_set(v___x_1178_, 4, v_r_1084_);
return v___x_1178_;
}
}
else
{
if (lean_obj_tag(v_l_1083_) == 0)
{
lean_object* v_l_1179_; 
v_l_1179_ = lean_ctor_get(v_l_1083_, 3);
if (lean_obj_tag(v_l_1179_) == 0)
{
lean_object* v_r_1180_; 
lean_inc_ref(v_l_1179_);
v_r_1180_ = lean_ctor_get(v_l_1083_, 4);
lean_inc(v_r_1180_);
if (lean_obj_tag(v_r_1180_) == 0)
{
lean_object* v_size_1181_; lean_object* v_k_1182_; lean_object* v_v_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1206_; 
v_size_1181_ = lean_ctor_get(v_l_1083_, 0);
v_k_1182_ = lean_ctor_get(v_l_1083_, 1);
v_v_1183_ = lean_ctor_get(v_l_1083_, 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_l_1083_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1207_ = lean_ctor_get(v_l_1083_, 4);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_l_1083_, 3);
lean_dec(v_unused_1208_);
v___x_1185_ = v_l_1083_;
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_v_1183_);
lean_inc(v_k_1182_);
lean_inc(v_size_1181_);
lean_dec(v_l_1083_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_size_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v_size_1187_ = lean_ctor_get(v_r_1180_, 0);
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v___x_1188_, v_size_1181_);
lean_dec(v_size_1181_);
v___x_1190_ = lean_nat_add(v___x_1188_, v_size_1187_);
lean_inc_ref(v_r_1180_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 4, v_r_1084_);
lean_ctor_set(v___x_1185_, 3, v_r_1180_);
lean_ctor_set(v___x_1185_, 2, v_v_1082_);
lean_ctor_set(v___x_1185_, 1, v_k_1081_);
lean_ctor_set(v___x_1185_, 0, v___x_1190_);
v___x_1192_ = v___x_1185_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_r_1180_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_r_1084_);
v___x_1192_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_isSharedCheck_1199_ = !lean_is_exclusive(v_r_1180_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; lean_object* v_unused_1201_; lean_object* v_unused_1202_; lean_object* v_unused_1203_; lean_object* v_unused_1204_; 
v_unused_1200_ = lean_ctor_get(v_r_1180_, 4);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_r_1180_, 3);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v_r_1180_, 2);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_r_1180_, 1);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_r_1180_, 0);
lean_dec(v_unused_1204_);
v___x_1194_ = v_r_1180_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v_r_1180_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 4, v___x_1192_);
lean_ctor_set(v___x_1194_, 3, v_l_1179_);
lean_ctor_set(v___x_1194_, 2, v_v_1183_);
lean_ctor_set(v___x_1194_, 1, v_k_1182_);
lean_ctor_set(v___x_1194_, 0, v___x_1189_);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_k_1182_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_v_1183_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v___x_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
else
{
lean_object* v_k_1209_; lean_object* v_v_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1220_; 
v_k_1209_ = lean_ctor_get(v_l_1083_, 1);
v_v_1210_ = lean_ctor_get(v_l_1083_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_l_1083_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; 
v_unused_1221_ = lean_ctor_get(v_l_1083_, 4);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_l_1083_, 3);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_l_1083_, 0);
lean_dec(v_unused_1223_);
v___x_1212_ = v_l_1083_;
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_v_1210_);
lean_inc(v_k_1209_);
lean_dec(v_l_1083_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1214_ = lean_unsigned_to_nat(3u);
v___x_1215_ = lean_unsigned_to_nat(1u);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 3, v_r_1180_);
lean_ctor_set(v___x_1212_, 2, v_v_1082_);
lean_ctor_set(v___x_1212_, 1, v_k_1081_);
lean_ctor_set(v___x_1212_, 0, v___x_1215_);
v___x_1217_ = v___x_1212_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_r_1180_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_r_1180_);
v___x_1217_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1214_);
lean_ctor_set(v___x_1218_, 1, v_k_1209_);
lean_ctor_set(v___x_1218_, 2, v_v_1210_);
lean_ctor_set(v___x_1218_, 3, v_l_1179_);
lean_ctor_set(v___x_1218_, 4, v___x_1217_);
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_r_1224_; 
v_r_1224_ = lean_ctor_get(v_l_1083_, 4);
lean_inc(v_r_1224_);
if (lean_obj_tag(v_r_1224_) == 0)
{
lean_object* v_k_1225_; lean_object* v_v_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1248_; 
lean_inc(v_l_1179_);
v_k_1225_ = lean_ctor_get(v_l_1083_, 1);
v_v_1226_ = lean_ctor_get(v_l_1083_, 2);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_l_1083_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; lean_object* v_unused_1250_; lean_object* v_unused_1251_; 
v_unused_1249_ = lean_ctor_get(v_l_1083_, 4);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v_l_1083_, 3);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_l_1083_, 0);
lean_dec(v_unused_1251_);
v___x_1228_ = v_l_1083_;
v_isShared_1229_ = v_isSharedCheck_1248_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_v_1226_);
lean_inc(v_k_1225_);
lean_dec(v_l_1083_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1248_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1244_; 
v_k_1230_ = lean_ctor_get(v_r_1224_, 1);
v_v_1231_ = lean_ctor_get(v_r_1224_, 2);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_r_1224_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; lean_object* v_unused_1246_; lean_object* v_unused_1247_; 
v_unused_1245_ = lean_ctor_get(v_r_1224_, 4);
lean_dec(v_unused_1245_);
v_unused_1246_ = lean_ctor_get(v_r_1224_, 3);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v_r_1224_, 0);
lean_dec(v_unused_1247_);
v___x_1233_ = v_r_1224_;
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_v_1231_);
lean_inc(v_k_1230_);
lean_dec(v_r_1224_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1235_ = lean_unsigned_to_nat(3u);
v___x_1236_ = lean_unsigned_to_nat(1u);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v_l_1179_);
lean_ctor_set(v___x_1233_, 3, v_l_1179_);
lean_ctor_set(v___x_1233_, 2, v_v_1226_);
lean_ctor_set(v___x_1233_, 1, v_k_1225_);
lean_ctor_set(v___x_1233_, 0, v___x_1236_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_k_1225_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_v_1226_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_l_1179_);
v___x_1238_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 4, v_l_1179_);
lean_ctor_set(v___x_1228_, 2, v_v_1082_);
lean_ctor_set(v___x_1228_, 1, v_k_1081_);
lean_ctor_set(v___x_1228_, 0, v___x_1236_);
v___x_1240_ = v___x_1228_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_l_1179_);
v___x_1240_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1235_);
lean_ctor_set(v___x_1241_, 1, v_k_1230_);
lean_ctor_set(v___x_1241_, 2, v_v_1231_);
lean_ctor_set(v___x_1241_, 3, v___x_1238_);
lean_ctor_set(v___x_1241_, 4, v___x_1240_);
return v___x_1241_;
}
}
}
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_unsigned_to_nat(2u);
v___x_1253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v_k_1081_);
lean_ctor_set(v___x_1253_, 2, v_v_1082_);
lean_ctor_set(v___x_1253_, 3, v_l_1083_);
lean_ctor_set(v___x_1253_, 4, v_r_1224_);
return v___x_1253_;
}
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v_k_1081_);
lean_ctor_set(v___x_1255_, 2, v_v_1082_);
lean_ctor_set(v___x_1255_, 3, v_l_1083_);
lean_ctor_set(v___x_1255_, 4, v_l_1083_);
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_k_1258_, lean_object* v_v_1259_, lean_object* v_l_1260_, lean_object* v_r_1261_){
_start:
{
if (lean_obj_tag(v_r_1261_) == 0)
{
if (lean_obj_tag(v_l_1260_) == 0)
{
lean_object* v_size_1262_; lean_object* v_size_1263_; lean_object* v_k_1264_; lean_object* v_v_1265_; lean_object* v_l_1266_; lean_object* v_r_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_size_1262_ = lean_ctor_get(v_r_1261_, 0);
v_size_1263_ = lean_ctor_get(v_l_1260_, 0);
v_k_1264_ = lean_ctor_get(v_l_1260_, 1);
v_v_1265_ = lean_ctor_get(v_l_1260_, 2);
v_l_1266_ = lean_ctor_get(v_l_1260_, 3);
v_r_1267_ = lean_ctor_get(v_l_1260_, 4);
lean_inc(v_r_1267_);
v___x_1268_ = lean_unsigned_to_nat(3u);
v___x_1269_ = lean_nat_mul(v___x_1268_, v_size_1262_);
v___x_1270_ = lean_nat_dec_lt(v___x_1269_, v_size_1263_);
lean_dec(v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec(v_r_1267_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v___x_1271_, v_size_1263_);
v___x_1273_ = lean_nat_add(v___x_1272_, v_size_1262_);
lean_dec(v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v_k_1258_);
lean_ctor_set(v___x_1274_, 2, v_v_1259_);
lean_ctor_set(v___x_1274_, 3, v_l_1260_);
lean_ctor_set(v___x_1274_, 4, v_r_1261_);
return v___x_1274_;
}
else
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1346_; 
lean_inc(v_l_1266_);
lean_inc(v_v_1265_);
lean_inc(v_k_1264_);
lean_inc(v_size_1263_);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_l_1260_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; lean_object* v_unused_1351_; 
v_unused_1347_ = lean_ctor_get(v_l_1260_, 4);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_l_1260_, 3);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_l_1260_, 2);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_l_1260_, 1);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_l_1260_, 0);
lean_dec(v_unused_1351_);
v___x_1276_ = v_l_1260_;
v_isShared_1277_ = v_isSharedCheck_1346_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v_l_1260_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1346_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
if (lean_obj_tag(v_l_1266_) == 0)
{
if (lean_obj_tag(v_r_1267_) == 0)
{
lean_object* v_size_1278_; lean_object* v_size_1279_; lean_object* v_k_1280_; lean_object* v_v_1281_; lean_object* v_l_1282_; lean_object* v_r_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_size_1278_ = lean_ctor_get(v_l_1266_, 0);
v_size_1279_ = lean_ctor_get(v_r_1267_, 0);
v_k_1280_ = lean_ctor_get(v_r_1267_, 1);
v_v_1281_ = lean_ctor_get(v_r_1267_, 2);
v_l_1282_ = lean_ctor_get(v_r_1267_, 3);
v_r_1283_ = lean_ctor_get(v_r_1267_, 4);
v___x_1284_ = lean_unsigned_to_nat(2u);
v___x_1285_ = lean_nat_mul(v___x_1284_, v_size_1278_);
v___x_1286_ = lean_nat_dec_lt(v_size_1279_, v___x_1285_);
lean_dec(v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1314_; 
lean_inc(v_r_1283_);
lean_inc(v_l_1282_);
lean_inc(v_v_1281_);
lean_inc(v_k_1280_);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_r_1267_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; lean_object* v_unused_1316_; lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; 
v_unused_1315_ = lean_ctor_get(v_r_1267_, 4);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_r_1267_, 3);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_r_1267_, 2);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_r_1267_, 1);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_r_1267_, 0);
lean_dec(v_unused_1319_);
v___x_1288_ = v_r_1267_;
v_isShared_1289_ = v_isSharedCheck_1314_;
goto v_resetjp_1287_;
}
else
{
lean_dec(v_r_1267_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1314_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___x_1304_; lean_object* v___y_1306_; 
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_nat_add(v___x_1290_, v_size_1263_);
lean_dec(v_size_1263_);
v___x_1292_ = lean_nat_add(v___x_1291_, v_size_1262_);
lean_dec(v___x_1291_);
v___x_1304_ = lean_nat_add(v___x_1290_, v_size_1278_);
if (lean_obj_tag(v_l_1282_) == 0)
{
lean_object* v_size_1312_; 
v_size_1312_ = lean_ctor_get(v_l_1282_, 0);
lean_inc(v_size_1312_);
v___y_1306_ = v_size_1312_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___y_1306_ = v___x_1313_;
goto v___jp_1305_;
}
v___jp_1293_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_nat_add(v___y_1294_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec(v___y_1294_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 4, v_r_1261_);
lean_ctor_set(v___x_1288_, 3, v_r_1283_);
lean_ctor_set(v___x_1288_, 2, v_v_1259_);
lean_ctor_set(v___x_1288_, 1, v_k_1258_);
lean_ctor_set(v___x_1288_, 0, v___x_1297_);
v___x_1299_ = v___x_1288_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1258_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1259_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_r_1283_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_r_1261_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 4, v___x_1299_);
lean_ctor_set(v___x_1276_, 3, v___y_1295_);
lean_ctor_set(v___x_1276_, 2, v_v_1281_);
lean_ctor_set(v___x_1276_, 1, v_k_1280_);
lean_ctor_set(v___x_1276_, 0, v___x_1292_);
v___x_1301_ = v___x_1276_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___y_1295_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_nat_add(v___x_1304_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec(v___x_1304_);
v___x_1308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_k_1264_);
lean_ctor_set(v___x_1308_, 2, v_v_1265_);
lean_ctor_set(v___x_1308_, 3, v_l_1266_);
lean_ctor_set(v___x_1308_, 4, v_l_1282_);
v___x_1309_ = lean_nat_add(v___x_1290_, v_size_1262_);
if (lean_obj_tag(v_r_1283_) == 0)
{
lean_object* v_size_1310_; 
v_size_1310_ = lean_ctor_get(v_r_1283_, 0);
lean_inc(v_size_1310_);
v___y_1294_ = v___x_1309_;
v___y_1295_ = v___x_1308_;
v___y_1296_ = v_size_1310_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___y_1294_ = v___x_1309_;
v___y_1295_ = v___x_1308_;
v___y_1296_ = v___x_1311_;
goto v___jp_1293_;
}
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v___x_1320_, v_size_1263_);
lean_dec(v_size_1263_);
v___x_1322_ = lean_nat_add(v___x_1321_, v_size_1262_);
lean_dec(v___x_1321_);
v___x_1323_ = lean_nat_add(v___x_1320_, v_size_1262_);
v___x_1324_ = lean_nat_add(v___x_1323_, v_size_1279_);
lean_dec(v___x_1323_);
lean_inc_ref(v_r_1261_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 4, v_r_1261_);
lean_ctor_set(v___x_1276_, 3, v_r_1267_);
lean_ctor_set(v___x_1276_, 2, v_v_1259_);
lean_ctor_set(v___x_1276_, 1, v_k_1258_);
lean_ctor_set(v___x_1276_, 0, v___x_1324_);
v___x_1326_ = v___x_1276_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1258_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1259_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_r_1267_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_r_1261_);
v___x_1326_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_isSharedCheck_1333_ = !lean_is_exclusive(v_r_1261_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; lean_object* v_unused_1335_; lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; 
v_unused_1334_ = lean_ctor_get(v_r_1261_, 4);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_r_1261_, 3);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_r_1261_, 2);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_r_1261_, 1);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_r_1261_, 0);
lean_dec(v_unused_1338_);
v___x_1328_ = v_r_1261_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_dec(v_r_1261_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v___x_1326_);
lean_ctor_set(v___x_1328_, 3, v_l_1266_);
lean_ctor_set(v___x_1328_, 2, v_v_1265_);
lean_ctor_set(v___x_1328_, 1, v_k_1264_);
lean_ctor_set(v___x_1328_, 0, v___x_1322_);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1264_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1265_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_l_1266_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v___x_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v_l_1266_);
lean_del_object(v___x_1276_);
lean_dec(v_v_1265_);
lean_dec(v_k_1264_);
lean_dec(v_size_1263_);
lean_dec_ref(v_r_1261_);
lean_dec(v_v_1259_);
lean_dec(v_k_1258_);
v___x_1340_ = lean_box(1);
v___x_1341_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
v___x_1342_ = l_panic___redArg(v___x_1340_, v___x_1341_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_del_object(v___x_1276_);
lean_dec(v_r_1267_);
lean_dec(v_v_1265_);
lean_dec(v_k_1264_);
lean_dec(v_size_1263_);
lean_dec_ref(v_r_1261_);
lean_dec(v_v_1259_);
lean_dec(v_k_1258_);
v___x_1343_ = lean_box(1);
v___x_1344_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
v___x_1345_ = l_panic___redArg(v___x_1343_, v___x_1344_);
return v___x_1345_;
}
}
}
}
else
{
lean_object* v_size_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_size_1352_ = lean_ctor_get(v_r_1261_, 0);
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_nat_add(v___x_1353_, v_size_1352_);
v___x_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_k_1258_);
lean_ctor_set(v___x_1355_, 2, v_v_1259_);
lean_ctor_set(v___x_1355_, 3, v_l_1260_);
lean_ctor_set(v___x_1355_, 4, v_r_1261_);
return v___x_1355_;
}
}
else
{
if (lean_obj_tag(v_l_1260_) == 0)
{
lean_object* v_l_1356_; 
v_l_1356_ = lean_ctor_get(v_l_1260_, 3);
if (lean_obj_tag(v_l_1356_) == 0)
{
lean_object* v_r_1357_; 
lean_inc_ref(v_l_1356_);
v_r_1357_ = lean_ctor_get(v_l_1260_, 4);
lean_inc(v_r_1357_);
if (lean_obj_tag(v_r_1357_) == 0)
{
lean_object* v_size_1358_; lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1383_; 
v_size_1358_ = lean_ctor_get(v_l_1260_, 0);
v_k_1359_ = lean_ctor_get(v_l_1260_, 1);
v_v_1360_ = lean_ctor_get(v_l_1260_, 2);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_l_1260_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; lean_object* v_unused_1385_; 
v_unused_1384_ = lean_ctor_get(v_l_1260_, 4);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_l_1260_, 3);
lean_dec(v_unused_1385_);
v___x_1362_ = v_l_1260_;
v_isShared_1363_ = v_isSharedCheck_1383_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_v_1360_);
lean_inc(v_k_1359_);
lean_inc(v_size_1358_);
lean_dec(v_l_1260_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1383_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_size_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v_size_1364_ = lean_ctor_get(v_r_1357_, 0);
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_nat_add(v___x_1365_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1367_ = lean_nat_add(v___x_1365_, v_size_1364_);
lean_inc_ref(v_r_1357_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_r_1261_);
lean_ctor_set(v___x_1362_, 3, v_r_1357_);
lean_ctor_set(v___x_1362_, 2, v_v_1259_);
lean_ctor_set(v___x_1362_, 1, v_k_1258_);
lean_ctor_set(v___x_1362_, 0, v___x_1367_);
v___x_1369_ = v___x_1362_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1258_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1259_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1357_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_r_1261_);
v___x_1369_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v_r_1357_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; lean_object* v_unused_1380_; lean_object* v_unused_1381_; 
v_unused_1377_ = lean_ctor_get(v_r_1357_, 4);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1357_, 3);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_r_1357_, 2);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_r_1357_, 1);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_r_1357_, 0);
lean_dec(v_unused_1381_);
v___x_1371_ = v_r_1357_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_r_1357_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1369_);
lean_ctor_set(v___x_1371_, 3, v_l_1356_);
lean_ctor_set(v___x_1371_, 2, v_v_1360_);
lean_ctor_set(v___x_1371_, 1, v_k_1359_);
lean_ctor_set(v___x_1371_, 0, v___x_1366_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1359_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_l_1356_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v___x_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
else
{
lean_object* v_k_1386_; lean_object* v_v_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v_k_1386_ = lean_ctor_get(v_l_1260_, 1);
v_v_1387_ = lean_ctor_get(v_l_1260_, 2);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_l_1260_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1398_ = lean_ctor_get(v_l_1260_, 4);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_l_1260_, 3);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_l_1260_, 0);
lean_dec(v_unused_1400_);
v___x_1389_ = v_l_1260_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_v_1387_);
lean_inc(v_k_1386_);
lean_dec(v_l_1260_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = lean_unsigned_to_nat(3u);
v___x_1392_ = lean_unsigned_to_nat(1u);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 3, v_r_1357_);
lean_ctor_set(v___x_1389_, 2, v_v_1259_);
lean_ctor_set(v___x_1389_, 1, v_k_1258_);
lean_ctor_set(v___x_1389_, 0, v___x_1392_);
v___x_1394_ = v___x_1389_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1258_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1259_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_r_1357_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_r_1357_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1391_);
lean_ctor_set(v___x_1395_, 1, v_k_1386_);
lean_ctor_set(v___x_1395_, 2, v_v_1387_);
lean_ctor_set(v___x_1395_, 3, v_l_1356_);
lean_ctor_set(v___x_1395_, 4, v___x_1394_);
return v___x_1395_;
}
}
}
}
else
{
lean_object* v_r_1401_; 
v_r_1401_ = lean_ctor_get(v_l_1260_, 4);
lean_inc(v_r_1401_);
if (lean_obj_tag(v_r_1401_) == 0)
{
lean_object* v_k_1402_; lean_object* v_v_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1425_; 
lean_inc(v_l_1356_);
v_k_1402_ = lean_ctor_get(v_l_1260_, 1);
v_v_1403_ = lean_ctor_get(v_l_1260_, 2);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_l_1260_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; 
v_unused_1426_ = lean_ctor_get(v_l_1260_, 4);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_l_1260_, 3);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_l_1260_, 0);
lean_dec(v_unused_1428_);
v___x_1405_ = v_l_1260_;
v_isShared_1406_ = v_isSharedCheck_1425_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_v_1403_);
lean_inc(v_k_1402_);
lean_dec(v_l_1260_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1425_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_k_1407_; lean_object* v_v_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1421_; 
v_k_1407_ = lean_ctor_get(v_r_1401_, 1);
v_v_1408_ = lean_ctor_get(v_r_1401_, 2);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_r_1401_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; lean_object* v_unused_1423_; lean_object* v_unused_1424_; 
v_unused_1422_ = lean_ctor_get(v_r_1401_, 4);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_r_1401_, 3);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_r_1401_, 0);
lean_dec(v_unused_1424_);
v___x_1410_ = v_r_1401_;
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_v_1408_);
lean_inc(v_k_1407_);
lean_dec(v_r_1401_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_unsigned_to_nat(3u);
v___x_1413_ = lean_unsigned_to_nat(1u);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v_l_1356_);
lean_ctor_set(v___x_1410_, 3, v_l_1356_);
lean_ctor_set(v___x_1410_, 2, v_v_1403_);
lean_ctor_set(v___x_1410_, 1, v_k_1402_);
lean_ctor_set(v___x_1410_, 0, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1402_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1403_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_l_1356_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_l_1356_);
v___x_1415_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 4, v_l_1356_);
lean_ctor_set(v___x_1405_, 2, v_v_1259_);
lean_ctor_set(v___x_1405_, 1, v_k_1258_);
lean_ctor_set(v___x_1405_, 0, v___x_1413_);
v___x_1417_ = v___x_1405_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1258_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1259_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_l_1356_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_l_1356_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1412_);
lean_ctor_set(v___x_1418_, 1, v_k_1407_);
lean_ctor_set(v___x_1418_, 2, v_v_1408_);
lean_ctor_set(v___x_1418_, 3, v___x_1415_);
lean_ctor_set(v___x_1418_, 4, v___x_1417_);
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_unsigned_to_nat(2u);
v___x_1430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v_k_1258_);
lean_ctor_set(v___x_1430_, 2, v_v_1259_);
lean_ctor_set(v___x_1430_, 3, v_l_1260_);
lean_ctor_set(v___x_1430_, 4, v_r_1401_);
return v___x_1430_;
}
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_k_1258_);
lean_ctor_set(v___x_1432_, 2, v_v_1259_);
lean_ctor_set(v___x_1432_, 3, v_l_1260_);
lean_ctor_set(v___x_1432_, 4, v_l_1260_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR___redArg(lean_object* v_k_1433_, lean_object* v_v_1434_, lean_object* v_l_1435_, lean_object* v_r_1436_){
_start:
{
if (lean_obj_tag(v_l_1435_) == 0)
{
if (lean_obj_tag(v_r_1436_) == 0)
{
lean_object* v_size_1437_; lean_object* v_size_1438_; lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v_l_1441_; lean_object* v_r_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_size_1437_ = lean_ctor_get(v_l_1435_, 0);
v_size_1438_ = lean_ctor_get(v_r_1436_, 0);
v_k_1439_ = lean_ctor_get(v_r_1436_, 1);
v_v_1440_ = lean_ctor_get(v_r_1436_, 2);
v_l_1441_ = lean_ctor_get(v_r_1436_, 3);
lean_inc(v_l_1441_);
v_r_1442_ = lean_ctor_get(v_r_1436_, 4);
v___x_1443_ = lean_unsigned_to_nat(3u);
v___x_1444_ = lean_nat_mul(v___x_1443_, v_size_1437_);
v___x_1445_ = lean_nat_dec_lt(v___x_1444_, v_size_1438_);
lean_dec(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec(v_l_1441_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1437_);
v___x_1448_ = lean_nat_add(v___x_1447_, v_size_1438_);
lean_dec(v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v_k_1433_);
lean_ctor_set(v___x_1449_, 2, v_v_1434_);
lean_ctor_set(v___x_1449_, 3, v_l_1435_);
lean_ctor_set(v___x_1449_, 4, v_r_1436_);
return v___x_1449_;
}
else
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1513_; 
lean_inc(v_r_1442_);
lean_inc(v_v_1440_);
lean_inc(v_k_1439_);
lean_inc(v_size_1438_);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_r_1436_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; 
v_unused_1514_ = lean_ctor_get(v_r_1436_, 4);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_r_1436_, 3);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_r_1436_, 2);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1436_, 1);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_r_1436_, 0);
lean_dec(v_unused_1518_);
v___x_1451_ = v_r_1436_;
v_isShared_1452_ = v_isSharedCheck_1513_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_r_1436_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1513_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_size_1453_; lean_object* v_k_1454_; lean_object* v_v_1455_; lean_object* v_l_1456_; lean_object* v_r_1457_; lean_object* v_size_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_size_1453_ = lean_ctor_get(v_l_1441_, 0);
v_k_1454_ = lean_ctor_get(v_l_1441_, 1);
v_v_1455_ = lean_ctor_get(v_l_1441_, 2);
v_l_1456_ = lean_ctor_get(v_l_1441_, 3);
v_r_1457_ = lean_ctor_get(v_l_1441_, 4);
v_size_1458_ = lean_ctor_get(v_r_1442_, 0);
v___x_1459_ = lean_unsigned_to_nat(2u);
v___x_1460_ = lean_nat_mul(v___x_1459_, v_size_1458_);
v___x_1461_ = lean_nat_dec_lt(v_size_1453_, v___x_1460_);
lean_dec(v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1488_; 
lean_inc(v_r_1457_);
lean_inc(v_l_1456_);
lean_inc(v_v_1455_);
lean_inc(v_k_1454_);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_l_1441_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; lean_object* v_unused_1490_; lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1489_ = lean_ctor_get(v_l_1441_, 4);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_l_1441_, 3);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v_l_1441_, 2);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_l_1441_, 1);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_l_1441_, 0);
lean_dec(v_unused_1493_);
v___x_1463_ = v_l_1441_;
v_isShared_1464_ = v_isSharedCheck_1488_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v_l_1441_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1488_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1480_; 
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v___x_1465_, v_size_1437_);
v___x_1467_ = lean_nat_add(v___x_1466_, v_size_1438_);
lean_dec(v_size_1438_);
if (lean_obj_tag(v_l_1456_) == 0)
{
lean_object* v_size_1486_; 
v_size_1486_ = lean_ctor_get(v_l_1456_, 0);
lean_inc(v_size_1486_);
v___y_1480_ = v_size_1486_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___y_1480_ = v___x_1487_;
goto v___jp_1479_;
}
v___jp_1468_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_nat_add(v___y_1469_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec(v___y_1469_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v_r_1442_);
lean_ctor_set(v___x_1463_, 3, v_r_1457_);
lean_ctor_set(v___x_1463_, 2, v_v_1440_);
lean_ctor_set(v___x_1463_, 1, v_k_1439_);
lean_ctor_set(v___x_1463_, 0, v___x_1472_);
v___x_1474_ = v___x_1463_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_r_1457_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_r_1442_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v___x_1474_);
lean_ctor_set(v___x_1451_, 3, v___y_1470_);
lean_ctor_set(v___x_1451_, 2, v_v_1455_);
lean_ctor_set(v___x_1451_, 1, v_k_1454_);
lean_ctor_set(v___x_1451_, 0, v___x_1467_);
v___x_1476_ = v___x_1451_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1454_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1455_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_nat_add(v___x_1466_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec(v___x_1466_);
v___x_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_k_1433_);
lean_ctor_set(v___x_1482_, 2, v_v_1434_);
lean_ctor_set(v___x_1482_, 3, v_l_1435_);
lean_ctor_set(v___x_1482_, 4, v_l_1456_);
v___x_1483_ = lean_nat_add(v___x_1465_, v_size_1458_);
if (lean_obj_tag(v_r_1457_) == 0)
{
lean_object* v_size_1484_; 
v_size_1484_ = lean_ctor_get(v_r_1457_, 0);
lean_inc(v_size_1484_);
v___y_1469_ = v___x_1483_;
v___y_1470_ = v___x_1482_;
v___y_1471_ = v_size_1484_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_unsigned_to_nat(0u);
v___y_1469_ = v___x_1483_;
v___y_1470_ = v___x_1482_;
v___y_1471_ = v___x_1485_;
goto v___jp_1468_;
}
}
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v___x_1494_, v_size_1437_);
v___x_1496_ = lean_nat_add(v___x_1495_, v_size_1438_);
lean_dec(v_size_1438_);
v___x_1497_ = lean_nat_add(v___x_1495_, v_size_1453_);
lean_dec(v___x_1495_);
lean_inc_ref(v_l_1435_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_l_1441_);
lean_ctor_set(v___x_1451_, 3, v_l_1435_);
lean_ctor_set(v___x_1451_, 2, v_v_1434_);
lean_ctor_set(v___x_1451_, 1, v_k_1433_);
lean_ctor_set(v___x_1451_, 0, v___x_1497_);
v___x_1499_ = v___x_1451_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_k_1433_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_v_1434_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_l_1435_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_l_1441_);
v___x_1499_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
v_isSharedCheck_1506_ = !lean_is_exclusive(v_l_1435_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1507_ = lean_ctor_get(v_l_1435_, 4);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_l_1435_, 3);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_l_1435_, 2);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_l_1435_, 1);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_l_1435_, 0);
lean_dec(v_unused_1511_);
v___x_1501_ = v_l_1435_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v_l_1435_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 4, v_r_1442_);
lean_ctor_set(v___x_1501_, 3, v___x_1499_);
lean_ctor_set(v___x_1501_, 2, v_v_1440_);
lean_ctor_set(v___x_1501_, 1, v_k_1439_);
lean_ctor_set(v___x_1501_, 0, v___x_1496_);
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1505_, 3, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1505_, 4, v_r_1442_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_size_1519_ = lean_ctor_get(v_l_1435_, 0);
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v___x_1520_, v_size_1519_);
v___x_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v_k_1433_);
lean_ctor_set(v___x_1522_, 2, v_v_1434_);
lean_ctor_set(v___x_1522_, 3, v_l_1435_);
lean_ctor_set(v___x_1522_, 4, v_r_1436_);
return v___x_1522_;
}
}
else
{
if (lean_obj_tag(v_r_1436_) == 0)
{
lean_object* v_l_1523_; 
v_l_1523_ = lean_ctor_get(v_r_1436_, 3);
lean_inc(v_l_1523_);
if (lean_obj_tag(v_l_1523_) == 0)
{
lean_object* v_r_1524_; lean_object* v_k_1525_; lean_object* v_v_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1548_; 
v_r_1524_ = lean_ctor_get(v_r_1436_, 4);
v_k_1525_ = lean_ctor_get(v_r_1436_, 1);
v_v_1526_ = lean_ctor_get(v_r_1436_, 2);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_r_1436_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; 
v_unused_1549_ = lean_ctor_get(v_r_1436_, 3);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_r_1436_, 0);
lean_dec(v_unused_1550_);
v___x_1528_ = v_r_1436_;
v_isShared_1529_ = v_isSharedCheck_1548_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_r_1524_);
lean_inc(v_v_1526_);
lean_inc(v_k_1525_);
lean_dec(v_r_1436_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1548_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_k_1530_; lean_object* v_v_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1544_; 
v_k_1530_ = lean_ctor_get(v_l_1523_, 1);
v_v_1531_ = lean_ctor_get(v_l_1523_, 2);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_l_1523_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; lean_object* v_unused_1546_; lean_object* v_unused_1547_; 
v_unused_1545_ = lean_ctor_get(v_l_1523_, 4);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_l_1523_, 3);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_l_1523_, 0);
lean_dec(v_unused_1547_);
v___x_1533_ = v_l_1523_;
v_isShared_1534_ = v_isSharedCheck_1544_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_v_1531_);
lean_inc(v_k_1530_);
lean_dec(v_l_1523_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1544_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = lean_unsigned_to_nat(3u);
v___x_1536_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_r_1524_, 2);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v_r_1524_);
lean_ctor_set(v___x_1533_, 3, v_r_1524_);
lean_ctor_set(v___x_1533_, 2, v_v_1434_);
lean_ctor_set(v___x_1533_, 1, v_k_1433_);
lean_ctor_set(v___x_1533_, 0, v___x_1536_);
v___x_1538_ = v___x_1533_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1433_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1434_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_r_1524_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_r_1524_);
v___x_1538_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
lean_inc(v_r_1524_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 3, v_r_1524_);
lean_ctor_set(v___x_1528_, 0, v___x_1536_);
v___x_1540_ = v___x_1528_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1525_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_r_1524_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_r_1524_);
v___x_1540_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1535_);
lean_ctor_set(v___x_1541_, 1, v_k_1530_);
lean_ctor_set(v___x_1541_, 2, v_v_1531_);
lean_ctor_set(v___x_1541_, 3, v___x_1538_);
lean_ctor_set(v___x_1541_, 4, v___x_1540_);
return v___x_1541_;
}
}
}
}
}
else
{
lean_object* v_r_1551_; 
v_r_1551_ = lean_ctor_get(v_r_1436_, 4);
lean_inc(v_r_1551_);
if (lean_obj_tag(v_r_1551_) == 0)
{
lean_object* v_k_1552_; lean_object* v_v_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1563_; 
v_k_1552_ = lean_ctor_get(v_r_1436_, 1);
v_v_1553_ = lean_ctor_get(v_r_1436_, 2);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_r_1436_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; lean_object* v_unused_1565_; lean_object* v_unused_1566_; 
v_unused_1564_ = lean_ctor_get(v_r_1436_, 4);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_r_1436_, 3);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_r_1436_, 0);
lean_dec(v_unused_1566_);
v___x_1555_ = v_r_1436_;
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_v_1553_);
lean_inc(v_k_1552_);
lean_dec(v_r_1436_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1557_ = lean_unsigned_to_nat(3u);
v___x_1558_ = lean_unsigned_to_nat(1u);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 4, v_l_1523_);
lean_ctor_set(v___x_1555_, 2, v_v_1434_);
lean_ctor_set(v___x_1555_, 1, v_k_1433_);
lean_ctor_set(v___x_1555_, 0, v___x_1558_);
v___x_1560_ = v___x_1555_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1433_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1434_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_l_1523_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_l_1523_);
v___x_1560_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1557_);
lean_ctor_set(v___x_1561_, 1, v_k_1552_);
lean_ctor_set(v___x_1561_, 2, v_v_1553_);
lean_ctor_set(v___x_1561_, 3, v___x_1560_);
lean_ctor_set(v___x_1561_, 4, v_r_1551_);
return v___x_1561_;
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_unsigned_to_nat(2u);
v___x_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v_k_1433_);
lean_ctor_set(v___x_1568_, 2, v_v_1434_);
lean_ctor_set(v___x_1568_, 3, v_r_1551_);
lean_ctor_set(v___x_1568_, 4, v_r_1436_);
return v___x_1568_;
}
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v_k_1433_);
lean_ctor_set(v___x_1570_, 2, v_v_1434_);
lean_ctor_set(v___x_1570_, 3, v_r_1436_);
lean_ctor_set(v___x_1570_, 4, v_r_1436_);
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR(lean_object* v_00_u03b1_1571_, lean_object* v_00_u03b2_1572_, lean_object* v_k_1573_, lean_object* v_v_1574_, lean_object* v_l_1575_, lean_object* v_r_1576_, lean_object* v_hlb_1577_, lean_object* v_hrb_1578_, lean_object* v_hlr_1579_){
_start:
{
if (lean_obj_tag(v_l_1575_) == 0)
{
if (lean_obj_tag(v_r_1576_) == 0)
{
lean_object* v_size_1580_; lean_object* v_size_1581_; lean_object* v_k_1582_; lean_object* v_v_1583_; lean_object* v_l_1584_; lean_object* v_r_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_size_1580_ = lean_ctor_get(v_l_1575_, 0);
v_size_1581_ = lean_ctor_get(v_r_1576_, 0);
v_k_1582_ = lean_ctor_get(v_r_1576_, 1);
v_v_1583_ = lean_ctor_get(v_r_1576_, 2);
v_l_1584_ = lean_ctor_get(v_r_1576_, 3);
lean_inc(v_l_1584_);
v_r_1585_ = lean_ctor_get(v_r_1576_, 4);
v___x_1586_ = lean_unsigned_to_nat(3u);
v___x_1587_ = lean_nat_mul(v___x_1586_, v_size_1580_);
v___x_1588_ = lean_nat_dec_lt(v___x_1587_, v_size_1581_);
lean_dec(v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_l_1584_);
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = lean_nat_add(v___x_1589_, v_size_1580_);
v___x_1591_ = lean_nat_add(v___x_1590_, v_size_1581_);
lean_dec(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v_k_1573_);
lean_ctor_set(v___x_1592_, 2, v_v_1574_);
lean_ctor_set(v___x_1592_, 3, v_l_1575_);
lean_ctor_set(v___x_1592_, 4, v_r_1576_);
return v___x_1592_;
}
else
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1656_; 
lean_inc(v_r_1585_);
lean_inc(v_v_1583_);
lean_inc(v_k_1582_);
lean_inc(v_size_1581_);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_r_1576_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; lean_object* v_unused_1658_; lean_object* v_unused_1659_; lean_object* v_unused_1660_; lean_object* v_unused_1661_; 
v_unused_1657_ = lean_ctor_get(v_r_1576_, 4);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_r_1576_, 3);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_r_1576_, 2);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_r_1576_, 1);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_r_1576_, 0);
lean_dec(v_unused_1661_);
v___x_1594_ = v_r_1576_;
v_isShared_1595_ = v_isSharedCheck_1656_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_r_1576_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1656_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_size_1596_; lean_object* v_k_1597_; lean_object* v_v_1598_; lean_object* v_l_1599_; lean_object* v_r_1600_; lean_object* v_size_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_size_1596_ = lean_ctor_get(v_l_1584_, 0);
v_k_1597_ = lean_ctor_get(v_l_1584_, 1);
v_v_1598_ = lean_ctor_get(v_l_1584_, 2);
v_l_1599_ = lean_ctor_get(v_l_1584_, 3);
v_r_1600_ = lean_ctor_get(v_l_1584_, 4);
v_size_1601_ = lean_ctor_get(v_r_1585_, 0);
v___x_1602_ = lean_unsigned_to_nat(2u);
v___x_1603_ = lean_nat_mul(v___x_1602_, v_size_1601_);
v___x_1604_ = lean_nat_dec_lt(v_size_1596_, v___x_1603_);
lean_dec(v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1631_; 
lean_inc(v_r_1600_);
lean_inc(v_l_1599_);
lean_inc(v_v_1598_);
lean_inc(v_k_1597_);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_l_1584_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; lean_object* v_unused_1633_; lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1632_ = lean_ctor_get(v_l_1584_, 4);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_l_1584_, 3);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v_l_1584_, 2);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_l_1584_, 1);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_l_1584_, 0);
lean_dec(v_unused_1636_);
v___x_1606_ = v_l_1584_;
v_isShared_1607_ = v_isSharedCheck_1631_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_l_1584_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1631_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1623_; 
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_add(v___x_1608_, v_size_1580_);
v___x_1610_ = lean_nat_add(v___x_1609_, v_size_1581_);
lean_dec(v_size_1581_);
if (lean_obj_tag(v_l_1599_) == 0)
{
lean_object* v_size_1629_; 
v_size_1629_ = lean_ctor_get(v_l_1599_, 0);
lean_inc(v_size_1629_);
v___y_1623_ = v_size_1629_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___y_1623_ = v___x_1630_;
goto v___jp_1622_;
}
v___jp_1611_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_nat_add(v___y_1612_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec(v___y_1612_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 4, v_r_1585_);
lean_ctor_set(v___x_1606_, 3, v_r_1600_);
lean_ctor_set(v___x_1606_, 2, v_v_1583_);
lean_ctor_set(v___x_1606_, 1, v_k_1582_);
lean_ctor_set(v___x_1606_, 0, v___x_1615_);
v___x_1617_ = v___x_1606_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_k_1582_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_v_1583_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v_r_1600_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v_r_1585_);
v___x_1617_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 4, v___x_1617_);
lean_ctor_set(v___x_1594_, 3, v___y_1613_);
lean_ctor_set(v___x_1594_, 2, v_v_1598_);
lean_ctor_set(v___x_1594_, 1, v_k_1597_);
lean_ctor_set(v___x_1594_, 0, v___x_1610_);
v___x_1619_ = v___x_1594_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1597_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1598_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v___y_1613_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
v___jp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = lean_nat_add(v___x_1609_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec(v___x_1609_);
v___x_1625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_k_1573_);
lean_ctor_set(v___x_1625_, 2, v_v_1574_);
lean_ctor_set(v___x_1625_, 3, v_l_1575_);
lean_ctor_set(v___x_1625_, 4, v_l_1599_);
v___x_1626_ = lean_nat_add(v___x_1608_, v_size_1601_);
if (lean_obj_tag(v_r_1600_) == 0)
{
lean_object* v_size_1627_; 
v_size_1627_ = lean_ctor_get(v_r_1600_, 0);
lean_inc(v_size_1627_);
v___y_1612_ = v___x_1626_;
v___y_1613_ = v___x_1625_;
v___y_1614_ = v_size_1627_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_unsigned_to_nat(0u);
v___y_1612_ = v___x_1626_;
v___y_1613_ = v___x_1625_;
v___y_1614_ = v___x_1628_;
goto v___jp_1611_;
}
}
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_add(v___x_1637_, v_size_1580_);
v___x_1639_ = lean_nat_add(v___x_1638_, v_size_1581_);
lean_dec(v_size_1581_);
v___x_1640_ = lean_nat_add(v___x_1638_, v_size_1596_);
lean_dec(v___x_1638_);
lean_inc_ref(v_l_1575_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 4, v_l_1584_);
lean_ctor_set(v___x_1594_, 3, v_l_1575_);
lean_ctor_set(v___x_1594_, 2, v_v_1574_);
lean_ctor_set(v___x_1594_, 1, v_k_1573_);
lean_ctor_set(v___x_1594_, 0, v___x_1640_);
v___x_1642_ = v___x_1594_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1573_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1574_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_l_1575_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_l_1584_);
v___x_1642_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_isSharedCheck_1649_ = !lean_is_exclusive(v_l_1575_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; lean_object* v_unused_1653_; lean_object* v_unused_1654_; 
v_unused_1650_ = lean_ctor_get(v_l_1575_, 4);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_l_1575_, 3);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_l_1575_, 2);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_l_1575_, 1);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_l_1575_, 0);
lean_dec(v_unused_1654_);
v___x_1644_ = v_l_1575_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_l_1575_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 4, v_r_1585_);
lean_ctor_set(v___x_1644_, 3, v___x_1642_);
lean_ctor_set(v___x_1644_, 2, v_v_1583_);
lean_ctor_set(v___x_1644_, 1, v_k_1582_);
lean_ctor_set(v___x_1644_, 0, v___x_1639_);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_k_1582_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_v_1583_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v_r_1585_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_size_1662_ = lean_ctor_get(v_l_1575_, 0);
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_nat_add(v___x_1663_, v_size_1662_);
v___x_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_k_1573_);
lean_ctor_set(v___x_1665_, 2, v_v_1574_);
lean_ctor_set(v___x_1665_, 3, v_l_1575_);
lean_ctor_set(v___x_1665_, 4, v_r_1576_);
return v___x_1665_;
}
}
else
{
if (lean_obj_tag(v_r_1576_) == 0)
{
lean_object* v_l_1666_; 
v_l_1666_ = lean_ctor_get(v_r_1576_, 3);
lean_inc(v_l_1666_);
if (lean_obj_tag(v_l_1666_) == 0)
{
lean_object* v_r_1667_; lean_object* v_k_1668_; lean_object* v_v_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1691_; 
v_r_1667_ = lean_ctor_get(v_r_1576_, 4);
v_k_1668_ = lean_ctor_get(v_r_1576_, 1);
v_v_1669_ = lean_ctor_get(v_r_1576_, 2);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_r_1576_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; lean_object* v_unused_1693_; 
v_unused_1692_ = lean_ctor_get(v_r_1576_, 3);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_r_1576_, 0);
lean_dec(v_unused_1693_);
v___x_1671_ = v_r_1576_;
v_isShared_1672_ = v_isSharedCheck_1691_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_r_1667_);
lean_inc(v_v_1669_);
lean_inc(v_k_1668_);
lean_dec(v_r_1576_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1691_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_k_1673_; lean_object* v_v_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1687_; 
v_k_1673_ = lean_ctor_get(v_l_1666_, 1);
v_v_1674_ = lean_ctor_get(v_l_1666_, 2);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_l_1666_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; 
v_unused_1688_ = lean_ctor_get(v_l_1666_, 4);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_l_1666_, 3);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_l_1666_, 0);
lean_dec(v_unused_1690_);
v___x_1676_ = v_l_1666_;
v_isShared_1677_ = v_isSharedCheck_1687_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_v_1674_);
lean_inc(v_k_1673_);
lean_dec(v_l_1666_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1687_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1678_ = lean_unsigned_to_nat(3u);
v___x_1679_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_r_1667_, 2);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v_r_1667_);
lean_ctor_set(v___x_1676_, 3, v_r_1667_);
lean_ctor_set(v___x_1676_, 2, v_v_1574_);
lean_ctor_set(v___x_1676_, 1, v_k_1573_);
lean_ctor_set(v___x_1676_, 0, v___x_1679_);
v___x_1681_ = v___x_1676_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1573_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1574_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_r_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_r_1667_);
v___x_1681_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
lean_inc(v_r_1667_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 3, v_r_1667_);
lean_ctor_set(v___x_1671_, 0, v___x_1679_);
v___x_1683_ = v___x_1671_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_k_1668_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_v_1669_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_r_1667_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_r_1667_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1678_);
lean_ctor_set(v___x_1684_, 1, v_k_1673_);
lean_ctor_set(v___x_1684_, 2, v_v_1674_);
lean_ctor_set(v___x_1684_, 3, v___x_1681_);
lean_ctor_set(v___x_1684_, 4, v___x_1683_);
return v___x_1684_;
}
}
}
}
}
else
{
lean_object* v_r_1694_; 
v_r_1694_ = lean_ctor_get(v_r_1576_, 4);
lean_inc(v_r_1694_);
if (lean_obj_tag(v_r_1694_) == 0)
{
lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1706_; 
v_k_1695_ = lean_ctor_get(v_r_1576_, 1);
v_v_1696_ = lean_ctor_get(v_r_1576_, 2);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_r_1576_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1707_ = lean_ctor_get(v_r_1576_, 4);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_r_1576_, 3);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_r_1576_, 0);
lean_dec(v_unused_1709_);
v___x_1698_ = v_r_1576_;
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_v_1696_);
lean_inc(v_k_1695_);
lean_dec(v_r_1576_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1700_ = lean_unsigned_to_nat(3u);
v___x_1701_ = lean_unsigned_to_nat(1u);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 4, v_l_1666_);
lean_ctor_set(v___x_1698_, 2, v_v_1574_);
lean_ctor_set(v___x_1698_, 1, v_k_1573_);
lean_ctor_set(v___x_1698_, 0, v___x_1701_);
v___x_1703_ = v___x_1698_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_k_1573_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_v_1574_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_l_1666_);
lean_ctor_set(v_reuseFailAlloc_1705_, 4, v_l_1666_);
v___x_1703_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1700_);
lean_ctor_set(v___x_1704_, 1, v_k_1695_);
lean_ctor_set(v___x_1704_, 2, v_v_1696_);
lean_ctor_set(v___x_1704_, 3, v___x_1703_);
lean_ctor_set(v___x_1704_, 4, v_r_1694_);
return v___x_1704_;
}
}
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_unsigned_to_nat(2u);
v___x_1711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v_k_1573_);
lean_ctor_set(v___x_1711_, 2, v_v_1574_);
lean_ctor_set(v___x_1711_, 3, v_r_1694_);
lean_ctor_set(v___x_1711_, 4, v_r_1576_);
return v___x_1711_;
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_unsigned_to_nat(1u);
v___x_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v_k_1573_);
lean_ctor_set(v___x_1713_, 2, v_v_1574_);
lean_ctor_set(v___x_1713_, 3, v_r_1576_);
lean_ctor_set(v___x_1713_, 4, v_r_1576_);
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase___redArg(lean_object* v_k_1714_, lean_object* v_v_1715_, lean_object* v_l_1716_, lean_object* v_r_1717_){
_start:
{
if (lean_obj_tag(v_l_1716_) == 0)
{
if (lean_obj_tag(v_r_1717_) == 0)
{
lean_object* v_size_1718_; lean_object* v_size_1719_; lean_object* v_k_1720_; lean_object* v_v_1721_; lean_object* v_l_1722_; lean_object* v_r_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_size_1718_ = lean_ctor_get(v_l_1716_, 0);
v_size_1719_ = lean_ctor_get(v_r_1717_, 0);
v_k_1720_ = lean_ctor_get(v_r_1717_, 1);
v_v_1721_ = lean_ctor_get(v_r_1717_, 2);
v_l_1722_ = lean_ctor_get(v_r_1717_, 3);
lean_inc(v_l_1722_);
v_r_1723_ = lean_ctor_get(v_r_1717_, 4);
v___x_1724_ = lean_unsigned_to_nat(3u);
v___x_1725_ = lean_nat_mul(v___x_1724_, v_size_1718_);
v___x_1726_ = lean_nat_dec_lt(v___x_1725_, v_size_1719_);
lean_dec(v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_l_1722_);
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v___x_1727_, v_size_1718_);
v___x_1729_ = lean_nat_add(v___x_1728_, v_size_1719_);
lean_dec(v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_k_1714_);
lean_ctor_set(v___x_1730_, 2, v_v_1715_);
lean_ctor_set(v___x_1730_, 3, v_l_1716_);
lean_ctor_set(v___x_1730_, 4, v_r_1717_);
return v___x_1730_;
}
else
{
lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1794_; 
lean_inc(v_r_1723_);
lean_inc(v_v_1721_);
lean_inc(v_k_1720_);
lean_inc(v_size_1719_);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_r_1717_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; 
v_unused_1795_ = lean_ctor_get(v_r_1717_, 4);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_r_1717_, 3);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_r_1717_, 2);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_r_1717_, 1);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_r_1717_, 0);
lean_dec(v_unused_1799_);
v___x_1732_ = v_r_1717_;
v_isShared_1733_ = v_isSharedCheck_1794_;
goto v_resetjp_1731_;
}
else
{
lean_dec(v_r_1717_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1794_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_size_1734_; lean_object* v_k_1735_; lean_object* v_v_1736_; lean_object* v_l_1737_; lean_object* v_r_1738_; lean_object* v_size_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_size_1734_ = lean_ctor_get(v_l_1722_, 0);
v_k_1735_ = lean_ctor_get(v_l_1722_, 1);
v_v_1736_ = lean_ctor_get(v_l_1722_, 2);
v_l_1737_ = lean_ctor_get(v_l_1722_, 3);
v_r_1738_ = lean_ctor_get(v_l_1722_, 4);
v_size_1739_ = lean_ctor_get(v_r_1723_, 0);
v___x_1740_ = lean_unsigned_to_nat(2u);
v___x_1741_ = lean_nat_mul(v___x_1740_, v_size_1739_);
v___x_1742_ = lean_nat_dec_lt(v_size_1734_, v___x_1741_);
lean_dec(v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1769_; 
lean_inc(v_r_1738_);
lean_inc(v_l_1737_);
lean_inc(v_v_1736_);
lean_inc(v_k_1735_);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_l_1722_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; 
v_unused_1770_ = lean_ctor_get(v_l_1722_, 4);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_l_1722_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_l_1722_, 2);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_l_1722_, 1);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_l_1722_, 0);
lean_dec(v_unused_1774_);
v___x_1744_ = v_l_1722_;
v_isShared_1745_ = v_isSharedCheck_1769_;
goto v_resetjp_1743_;
}
else
{
lean_dec(v_l_1722_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1769_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1761_; 
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_nat_add(v___x_1746_, v_size_1718_);
v___x_1748_ = lean_nat_add(v___x_1747_, v_size_1719_);
lean_dec(v_size_1719_);
if (lean_obj_tag(v_l_1737_) == 0)
{
lean_object* v_size_1767_; 
v_size_1767_ = lean_ctor_get(v_l_1737_, 0);
lean_inc(v_size_1767_);
v___y_1761_ = v_size_1767_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___y_1761_ = v___x_1768_;
goto v___jp_1760_;
}
v___jp_1749_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_nat_add(v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec(v___y_1751_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 4, v_r_1723_);
lean_ctor_set(v___x_1744_, 3, v_r_1738_);
lean_ctor_set(v___x_1744_, 2, v_v_1721_);
lean_ctor_set(v___x_1744_, 1, v_k_1720_);
lean_ctor_set(v___x_1744_, 0, v___x_1753_);
v___x_1755_ = v___x_1744_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_k_1720_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_v_1721_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_r_1738_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_r_1723_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 4, v___x_1755_);
lean_ctor_set(v___x_1732_, 3, v___y_1750_);
lean_ctor_set(v___x_1732_, 2, v_v_1736_);
lean_ctor_set(v___x_1732_, 1, v_k_1735_);
lean_ctor_set(v___x_1732_, 0, v___x_1748_);
v___x_1757_ = v___x_1732_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_k_1735_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_v_1736_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v___y_1750_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
v___jp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = lean_nat_add(v___x_1747_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec(v___x_1747_);
v___x_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_k_1714_);
lean_ctor_set(v___x_1763_, 2, v_v_1715_);
lean_ctor_set(v___x_1763_, 3, v_l_1716_);
lean_ctor_set(v___x_1763_, 4, v_l_1737_);
v___x_1764_ = lean_nat_add(v___x_1746_, v_size_1739_);
if (lean_obj_tag(v_r_1738_) == 0)
{
lean_object* v_size_1765_; 
v_size_1765_ = lean_ctor_get(v_r_1738_, 0);
lean_inc(v_size_1765_);
v___y_1750_ = v___x_1763_;
v___y_1751_ = v___x_1764_;
v___y_1752_ = v_size_1765_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_unsigned_to_nat(0u);
v___y_1750_ = v___x_1763_;
v___y_1751_ = v___x_1764_;
v___y_1752_ = v___x_1766_;
goto v___jp_1749_;
}
}
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v___x_1775_, v_size_1718_);
v___x_1777_ = lean_nat_add(v___x_1776_, v_size_1719_);
lean_dec(v_size_1719_);
v___x_1778_ = lean_nat_add(v___x_1776_, v_size_1734_);
lean_dec(v___x_1776_);
lean_inc_ref(v_l_1716_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 4, v_l_1722_);
lean_ctor_set(v___x_1732_, 3, v_l_1716_);
lean_ctor_set(v___x_1732_, 2, v_v_1715_);
lean_ctor_set(v___x_1732_, 1, v_k_1714_);
lean_ctor_set(v___x_1732_, 0, v___x_1778_);
v___x_1780_ = v___x_1732_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_k_1714_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v_v_1715_);
lean_ctor_set(v_reuseFailAlloc_1793_, 3, v_l_1716_);
lean_ctor_set(v_reuseFailAlloc_1793_, 4, v_l_1722_);
v___x_1780_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_isSharedCheck_1787_ = !lean_is_exclusive(v_l_1716_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; 
v_unused_1788_ = lean_ctor_get(v_l_1716_, 4);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_l_1716_, 3);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_l_1716_, 2);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_l_1716_, 1);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_l_1716_, 0);
lean_dec(v_unused_1792_);
v___x_1782_ = v_l_1716_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_dec(v_l_1716_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 4, v_r_1723_);
lean_ctor_set(v___x_1782_, 3, v___x_1780_);
lean_ctor_set(v___x_1782_, 2, v_v_1721_);
lean_ctor_set(v___x_1782_, 1, v_k_1720_);
lean_ctor_set(v___x_1782_, 0, v___x_1777_);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_k_1720_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_v_1721_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_r_1723_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_size_1800_ = lean_ctor_get(v_l_1716_, 0);
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_nat_add(v___x_1801_, v_size_1800_);
v___x_1803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v_k_1714_);
lean_ctor_set(v___x_1803_, 2, v_v_1715_);
lean_ctor_set(v___x_1803_, 3, v_l_1716_);
lean_ctor_set(v___x_1803_, 4, v_r_1717_);
return v___x_1803_;
}
}
else
{
if (lean_obj_tag(v_r_1717_) == 0)
{
lean_object* v_l_1804_; 
v_l_1804_ = lean_ctor_get(v_r_1717_, 3);
lean_inc(v_l_1804_);
if (lean_obj_tag(v_l_1804_) == 0)
{
lean_object* v_r_1805_; 
v_r_1805_ = lean_ctor_get(v_r_1717_, 4);
lean_inc(v_r_1805_);
if (lean_obj_tag(v_r_1805_) == 0)
{
lean_object* v_size_1806_; lean_object* v_k_1807_; lean_object* v_v_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1820_; 
v_size_1806_ = lean_ctor_get(v_r_1717_, 0);
v_k_1807_ = lean_ctor_get(v_r_1717_, 1);
v_v_1808_ = lean_ctor_get(v_r_1717_, 2);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_r_1717_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; lean_object* v_unused_1822_; 
v_unused_1821_ = lean_ctor_get(v_r_1717_, 4);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v_r_1717_, 3);
lean_dec(v_unused_1822_);
v___x_1810_ = v_r_1717_;
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_v_1808_);
lean_inc(v_k_1807_);
lean_inc(v_size_1806_);
lean_dec(v_r_1717_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_size_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v_size_1812_ = lean_ctor_get(v_l_1804_, 0);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_add(v___x_1813_, v_size_1806_);
lean_dec(v_size_1806_);
v___x_1815_ = lean_nat_add(v___x_1813_, v_size_1812_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_l_1804_);
lean_ctor_set(v___x_1810_, 3, v_l_1716_);
lean_ctor_set(v___x_1810_, 2, v_v_1715_);
lean_ctor_set(v___x_1810_, 1, v_k_1714_);
lean_ctor_set(v___x_1810_, 0, v___x_1815_);
v___x_1817_ = v___x_1810_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_k_1714_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_v_1715_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_l_1716_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_l_1804_);
v___x_1817_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1814_);
lean_ctor_set(v___x_1818_, 1, v_k_1807_);
lean_ctor_set(v___x_1818_, 2, v_v_1808_);
lean_ctor_set(v___x_1818_, 3, v___x_1817_);
lean_ctor_set(v___x_1818_, 4, v_r_1805_);
return v___x_1818_;
}
}
}
else
{
lean_object* v_k_1823_; lean_object* v_v_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1846_; 
v_k_1823_ = lean_ctor_get(v_r_1717_, 1);
v_v_1824_ = lean_ctor_get(v_r_1717_, 2);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_r_1717_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; 
v_unused_1847_ = lean_ctor_get(v_r_1717_, 4);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v_r_1717_, 3);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_r_1717_, 0);
lean_dec(v_unused_1849_);
v___x_1826_ = v_r_1717_;
v_isShared_1827_ = v_isSharedCheck_1846_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_v_1824_);
lean_inc(v_k_1823_);
lean_dec(v_r_1717_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1846_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_k_1828_; lean_object* v_v_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1842_; 
v_k_1828_ = lean_ctor_get(v_l_1804_, 1);
v_v_1829_ = lean_ctor_get(v_l_1804_, 2);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_l_1804_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; lean_object* v_unused_1844_; lean_object* v_unused_1845_; 
v_unused_1843_ = lean_ctor_get(v_l_1804_, 4);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v_l_1804_, 3);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v_l_1804_, 0);
lean_dec(v_unused_1845_);
v___x_1831_ = v_l_1804_;
v_isShared_1832_ = v_isSharedCheck_1842_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_v_1829_);
lean_inc(v_k_1828_);
lean_dec(v_l_1804_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1842_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1833_ = lean_unsigned_to_nat(3u);
v___x_1834_ = lean_unsigned_to_nat(1u);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 4, v_r_1805_);
lean_ctor_set(v___x_1831_, 3, v_r_1805_);
lean_ctor_set(v___x_1831_, 2, v_v_1715_);
lean_ctor_set(v___x_1831_, 1, v_k_1714_);
lean_ctor_set(v___x_1831_, 0, v___x_1834_);
v___x_1836_ = v___x_1831_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_k_1714_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_v_1715_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_r_1805_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_r_1805_);
v___x_1836_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 3, v_r_1805_);
lean_ctor_set(v___x_1826_, 0, v___x_1834_);
v___x_1838_ = v___x_1826_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_k_1823_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_v_1824_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v_r_1805_);
lean_ctor_set(v_reuseFailAlloc_1840_, 4, v_r_1805_);
v___x_1838_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1833_);
lean_ctor_set(v___x_1839_, 1, v_k_1828_);
lean_ctor_set(v___x_1839_, 2, v_v_1829_);
lean_ctor_set(v___x_1839_, 3, v___x_1836_);
lean_ctor_set(v___x_1839_, 4, v___x_1838_);
return v___x_1839_;
}
}
}
}
}
}
else
{
lean_object* v_r_1850_; 
v_r_1850_ = lean_ctor_get(v_r_1717_, 4);
lean_inc(v_r_1850_);
if (lean_obj_tag(v_r_1850_) == 0)
{
lean_object* v_k_1851_; lean_object* v_v_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1862_; 
v_k_1851_ = lean_ctor_get(v_r_1717_, 1);
v_v_1852_ = lean_ctor_get(v_r_1717_, 2);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_r_1717_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; 
v_unused_1863_ = lean_ctor_get(v_r_1717_, 4);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_r_1717_, 3);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_r_1717_, 0);
lean_dec(v_unused_1865_);
v___x_1854_ = v_r_1717_;
v_isShared_1855_ = v_isSharedCheck_1862_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_v_1852_);
lean_inc(v_k_1851_);
lean_dec(v_r_1717_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1862_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1856_ = lean_unsigned_to_nat(3u);
v___x_1857_ = lean_unsigned_to_nat(1u);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 4, v_l_1804_);
lean_ctor_set(v___x_1854_, 2, v_v_1715_);
lean_ctor_set(v___x_1854_, 1, v_k_1714_);
lean_ctor_set(v___x_1854_, 0, v___x_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_k_1714_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_v_1715_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_l_1804_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_l_1804_);
v___x_1859_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1856_);
lean_ctor_set(v___x_1860_, 1, v_k_1851_);
lean_ctor_set(v___x_1860_, 2, v_v_1852_);
lean_ctor_set(v___x_1860_, 3, v___x_1859_);
lean_ctor_set(v___x_1860_, 4, v_r_1850_);
return v___x_1860_;
}
}
}
else
{
lean_object* v_size_1866_; lean_object* v_k_1867_; lean_object* v_v_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1877_; 
v_size_1866_ = lean_ctor_get(v_r_1717_, 0);
v_k_1867_ = lean_ctor_get(v_r_1717_, 1);
v_v_1868_ = lean_ctor_get(v_r_1717_, 2);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_r_1717_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; lean_object* v_unused_1879_; 
v_unused_1878_ = lean_ctor_get(v_r_1717_, 4);
lean_dec(v_unused_1878_);
v_unused_1879_ = lean_ctor_get(v_r_1717_, 3);
lean_dec(v_unused_1879_);
v___x_1870_ = v_r_1717_;
v_isShared_1871_ = v_isSharedCheck_1877_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_v_1868_);
lean_inc(v_k_1867_);
lean_inc(v_size_1866_);
lean_dec(v_r_1717_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1877_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 3, v_r_1850_);
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_size_1866_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_r_1850_);
lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_r_1850_);
v___x_1873_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_unsigned_to_nat(2u);
v___x_1875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_k_1714_);
lean_ctor_set(v___x_1875_, 2, v_v_1715_);
lean_ctor_set(v___x_1875_, 3, v_r_1850_);
lean_ctor_set(v___x_1875_, 4, v___x_1873_);
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v_k_1714_);
lean_ctor_set(v___x_1881_, 2, v_v_1715_);
lean_ctor_set(v___x_1881_, 3, v_r_1717_);
lean_ctor_set(v___x_1881_, 4, v_r_1717_);
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase(lean_object* v_00_u03b1_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_k_1884_, lean_object* v_v_1885_, lean_object* v_l_1886_, lean_object* v_r_1887_, lean_object* v_hlb_1888_, lean_object* v_hrb_1889_, lean_object* v_hlr_1890_){
_start:
{
if (lean_obj_tag(v_l_1886_) == 0)
{
if (lean_obj_tag(v_r_1887_) == 0)
{
lean_object* v_size_1891_; lean_object* v_size_1892_; lean_object* v_k_1893_; lean_object* v_v_1894_; lean_object* v_l_1895_; lean_object* v_r_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v_size_1891_ = lean_ctor_get(v_l_1886_, 0);
v_size_1892_ = lean_ctor_get(v_r_1887_, 0);
v_k_1893_ = lean_ctor_get(v_r_1887_, 1);
v_v_1894_ = lean_ctor_get(v_r_1887_, 2);
v_l_1895_ = lean_ctor_get(v_r_1887_, 3);
lean_inc(v_l_1895_);
v_r_1896_ = lean_ctor_get(v_r_1887_, 4);
v___x_1897_ = lean_unsigned_to_nat(3u);
v___x_1898_ = lean_nat_mul(v___x_1897_, v_size_1891_);
v___x_1899_ = lean_nat_dec_lt(v___x_1898_, v_size_1892_);
lean_dec(v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v_l_1895_);
v___x_1900_ = lean_unsigned_to_nat(1u);
v___x_1901_ = lean_nat_add(v___x_1900_, v_size_1891_);
v___x_1902_ = lean_nat_add(v___x_1901_, v_size_1892_);
lean_dec(v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_k_1884_);
lean_ctor_set(v___x_1903_, 2, v_v_1885_);
lean_ctor_set(v___x_1903_, 3, v_l_1886_);
lean_ctor_set(v___x_1903_, 4, v_r_1887_);
return v___x_1903_;
}
else
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1967_; 
lean_inc(v_r_1896_);
lean_inc(v_v_1894_);
lean_inc(v_k_1893_);
lean_inc(v_size_1892_);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_r_1887_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; lean_object* v_unused_1972_; 
v_unused_1968_ = lean_ctor_get(v_r_1887_, 4);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_r_1887_, 3);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_r_1887_, 2);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_r_1887_, 1);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_r_1887_, 0);
lean_dec(v_unused_1972_);
v___x_1905_ = v_r_1887_;
v_isShared_1906_ = v_isSharedCheck_1967_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v_r_1887_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1967_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_size_1907_; lean_object* v_k_1908_; lean_object* v_v_1909_; lean_object* v_l_1910_; lean_object* v_r_1911_; lean_object* v_size_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v_size_1907_ = lean_ctor_get(v_l_1895_, 0);
v_k_1908_ = lean_ctor_get(v_l_1895_, 1);
v_v_1909_ = lean_ctor_get(v_l_1895_, 2);
v_l_1910_ = lean_ctor_get(v_l_1895_, 3);
v_r_1911_ = lean_ctor_get(v_l_1895_, 4);
v_size_1912_ = lean_ctor_get(v_r_1896_, 0);
v___x_1913_ = lean_unsigned_to_nat(2u);
v___x_1914_ = lean_nat_mul(v___x_1913_, v_size_1912_);
v___x_1915_ = lean_nat_dec_lt(v_size_1907_, v___x_1914_);
lean_dec(v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1942_; 
lean_inc(v_r_1911_);
lean_inc(v_l_1910_);
lean_inc(v_v_1909_);
lean_inc(v_k_1908_);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_l_1895_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; lean_object* v_unused_1944_; lean_object* v_unused_1945_; lean_object* v_unused_1946_; lean_object* v_unused_1947_; 
v_unused_1943_ = lean_ctor_get(v_l_1895_, 4);
lean_dec(v_unused_1943_);
v_unused_1944_ = lean_ctor_get(v_l_1895_, 3);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_l_1895_, 2);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_l_1895_, 1);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_l_1895_, 0);
lean_dec(v_unused_1947_);
v___x_1917_ = v_l_1895_;
v_isShared_1918_ = v_isSharedCheck_1942_;
goto v_resetjp_1916_;
}
else
{
lean_dec(v_l_1895_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1942_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1934_; 
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_nat_add(v___x_1919_, v_size_1891_);
v___x_1921_ = lean_nat_add(v___x_1920_, v_size_1892_);
lean_dec(v_size_1892_);
if (lean_obj_tag(v_l_1910_) == 0)
{
lean_object* v_size_1940_; 
v_size_1940_ = lean_ctor_get(v_l_1910_, 0);
lean_inc(v_size_1940_);
v___y_1934_ = v_size_1940_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___y_1934_ = v___x_1941_;
goto v___jp_1933_;
}
v___jp_1922_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_nat_add(v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec(v___y_1924_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 4, v_r_1896_);
lean_ctor_set(v___x_1917_, 3, v_r_1911_);
lean_ctor_set(v___x_1917_, 2, v_v_1894_);
lean_ctor_set(v___x_1917_, 1, v_k_1893_);
lean_ctor_set(v___x_1917_, 0, v___x_1926_);
v___x_1928_ = v___x_1917_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1893_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1894_);
lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_r_1911_);
lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_r_1896_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1930_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v___x_1928_);
lean_ctor_set(v___x_1905_, 3, v___y_1923_);
lean_ctor_set(v___x_1905_, 2, v_v_1909_);
lean_ctor_set(v___x_1905_, 1, v_k_1908_);
lean_ctor_set(v___x_1905_, 0, v___x_1921_);
v___x_1930_ = v___x_1905_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1908_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1909_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v___y_1923_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
v___jp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_nat_add(v___x_1920_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec(v___x_1920_);
v___x_1936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v_k_1884_);
lean_ctor_set(v___x_1936_, 2, v_v_1885_);
lean_ctor_set(v___x_1936_, 3, v_l_1886_);
lean_ctor_set(v___x_1936_, 4, v_l_1910_);
v___x_1937_ = lean_nat_add(v___x_1919_, v_size_1912_);
if (lean_obj_tag(v_r_1911_) == 0)
{
lean_object* v_size_1938_; 
v_size_1938_ = lean_ctor_get(v_r_1911_, 0);
lean_inc(v_size_1938_);
v___y_1923_ = v___x_1936_;
v___y_1924_ = v___x_1937_;
v___y_1925_ = v_size_1938_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_unsigned_to_nat(0u);
v___y_1923_ = v___x_1936_;
v___y_1924_ = v___x_1937_;
v___y_1925_ = v___x_1939_;
goto v___jp_1922_;
}
}
}
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1948_ = lean_unsigned_to_nat(1u);
v___x_1949_ = lean_nat_add(v___x_1948_, v_size_1891_);
v___x_1950_ = lean_nat_add(v___x_1949_, v_size_1892_);
lean_dec(v_size_1892_);
v___x_1951_ = lean_nat_add(v___x_1949_, v_size_1907_);
lean_dec(v___x_1949_);
lean_inc_ref(v_l_1886_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v_l_1895_);
lean_ctor_set(v___x_1905_, 3, v_l_1886_);
lean_ctor_set(v___x_1905_, 2, v_v_1885_);
lean_ctor_set(v___x_1905_, 1, v_k_1884_);
lean_ctor_set(v___x_1905_, 0, v___x_1951_);
v___x_1953_ = v___x_1905_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_l_1886_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_l_1895_);
v___x_1953_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_isSharedCheck_1960_ = !lean_is_exclusive(v_l_1886_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; lean_object* v_unused_1962_; lean_object* v_unused_1963_; lean_object* v_unused_1964_; lean_object* v_unused_1965_; 
v_unused_1961_ = lean_ctor_get(v_l_1886_, 4);
lean_dec(v_unused_1961_);
v_unused_1962_ = lean_ctor_get(v_l_1886_, 3);
lean_dec(v_unused_1962_);
v_unused_1963_ = lean_ctor_get(v_l_1886_, 2);
lean_dec(v_unused_1963_);
v_unused_1964_ = lean_ctor_get(v_l_1886_, 1);
lean_dec(v_unused_1964_);
v_unused_1965_ = lean_ctor_get(v_l_1886_, 0);
lean_dec(v_unused_1965_);
v___x_1955_ = v_l_1886_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_dec(v_l_1886_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 4, v_r_1896_);
lean_ctor_set(v___x_1955_, 3, v___x_1953_);
lean_ctor_set(v___x_1955_, 2, v_v_1894_);
lean_ctor_set(v___x_1955_, 1, v_k_1893_);
lean_ctor_set(v___x_1955_, 0, v___x_1950_);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_k_1893_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_v_1894_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v_r_1896_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_size_1973_ = lean_ctor_get(v_l_1886_, 0);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_add(v___x_1974_, v_size_1973_);
v___x_1976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v_k_1884_);
lean_ctor_set(v___x_1976_, 2, v_v_1885_);
lean_ctor_set(v___x_1976_, 3, v_l_1886_);
lean_ctor_set(v___x_1976_, 4, v_r_1887_);
return v___x_1976_;
}
}
else
{
if (lean_obj_tag(v_r_1887_) == 0)
{
lean_object* v_l_1977_; 
v_l_1977_ = lean_ctor_get(v_r_1887_, 3);
lean_inc(v_l_1977_);
if (lean_obj_tag(v_l_1977_) == 0)
{
lean_object* v_r_1978_; 
v_r_1978_ = lean_ctor_get(v_r_1887_, 4);
lean_inc(v_r_1978_);
if (lean_obj_tag(v_r_1978_) == 0)
{
lean_object* v_size_1979_; lean_object* v_k_1980_; lean_object* v_v_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1993_; 
v_size_1979_ = lean_ctor_get(v_r_1887_, 0);
v_k_1980_ = lean_ctor_get(v_r_1887_, 1);
v_v_1981_ = lean_ctor_get(v_r_1887_, 2);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_r_1887_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; lean_object* v_unused_1995_; 
v_unused_1994_ = lean_ctor_get(v_r_1887_, 4);
lean_dec(v_unused_1994_);
v_unused_1995_ = lean_ctor_get(v_r_1887_, 3);
lean_dec(v_unused_1995_);
v___x_1983_ = v_r_1887_;
v_isShared_1984_ = v_isSharedCheck_1993_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_v_1981_);
lean_inc(v_k_1980_);
lean_inc(v_size_1979_);
lean_dec(v_r_1887_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1993_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_size_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v_size_1985_ = lean_ctor_get(v_l_1977_, 0);
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_add(v___x_1986_, v_size_1979_);
lean_dec(v_size_1979_);
v___x_1988_ = lean_nat_add(v___x_1986_, v_size_1985_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v_l_1977_);
lean_ctor_set(v___x_1983_, 3, v_l_1886_);
lean_ctor_set(v___x_1983_, 2, v_v_1885_);
lean_ctor_set(v___x_1983_, 1, v_k_1884_);
lean_ctor_set(v___x_1983_, 0, v___x_1988_);
v___x_1990_ = v___x_1983_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v_l_1886_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v_l_1977_);
v___x_1990_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1987_);
lean_ctor_set(v___x_1991_, 1, v_k_1980_);
lean_ctor_set(v___x_1991_, 2, v_v_1981_);
lean_ctor_set(v___x_1991_, 3, v___x_1990_);
lean_ctor_set(v___x_1991_, 4, v_r_1978_);
return v___x_1991_;
}
}
}
else
{
lean_object* v_k_1996_; lean_object* v_v_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2019_; 
v_k_1996_ = lean_ctor_get(v_r_1887_, 1);
v_v_1997_ = lean_ctor_get(v_r_1887_, 2);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_r_1887_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; 
v_unused_2020_ = lean_ctor_get(v_r_1887_, 4);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_r_1887_, 3);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_r_1887_, 0);
lean_dec(v_unused_2022_);
v___x_1999_ = v_r_1887_;
v_isShared_2000_ = v_isSharedCheck_2019_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_v_1997_);
lean_inc(v_k_1996_);
lean_dec(v_r_1887_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2019_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v_k_2001_; lean_object* v_v_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2015_; 
v_k_2001_ = lean_ctor_get(v_l_1977_, 1);
v_v_2002_ = lean_ctor_get(v_l_1977_, 2);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_l_1977_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; lean_object* v_unused_2017_; lean_object* v_unused_2018_; 
v_unused_2016_ = lean_ctor_get(v_l_1977_, 4);
lean_dec(v_unused_2016_);
v_unused_2017_ = lean_ctor_get(v_l_1977_, 3);
lean_dec(v_unused_2017_);
v_unused_2018_ = lean_ctor_get(v_l_1977_, 0);
lean_dec(v_unused_2018_);
v___x_2004_ = v_l_1977_;
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_v_2002_);
lean_inc(v_k_2001_);
lean_dec(v_l_1977_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2006_ = lean_unsigned_to_nat(3u);
v___x_2007_ = lean_unsigned_to_nat(1u);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 4, v_r_1978_);
lean_ctor_set(v___x_2004_, 3, v_r_1978_);
lean_ctor_set(v___x_2004_, 2, v_v_1885_);
lean_ctor_set(v___x_2004_, 1, v_k_1884_);
lean_ctor_set(v___x_2004_, 0, v___x_2007_);
v___x_2009_ = v___x_2004_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_r_1978_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_r_1978_);
v___x_2009_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 3, v_r_1978_);
lean_ctor_set(v___x_1999_, 0, v___x_2007_);
v___x_2011_ = v___x_1999_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_r_1978_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_r_1978_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2006_);
lean_ctor_set(v___x_2012_, 1, v_k_2001_);
lean_ctor_set(v___x_2012_, 2, v_v_2002_);
lean_ctor_set(v___x_2012_, 3, v___x_2009_);
lean_ctor_set(v___x_2012_, 4, v___x_2011_);
return v___x_2012_;
}
}
}
}
}
}
else
{
lean_object* v_r_2023_; 
v_r_2023_ = lean_ctor_get(v_r_1887_, 4);
lean_inc(v_r_2023_);
if (lean_obj_tag(v_r_2023_) == 0)
{
lean_object* v_k_2024_; lean_object* v_v_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2035_; 
v_k_2024_ = lean_ctor_get(v_r_1887_, 1);
v_v_2025_ = lean_ctor_get(v_r_1887_, 2);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_r_1887_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; lean_object* v_unused_2037_; lean_object* v_unused_2038_; 
v_unused_2036_ = lean_ctor_get(v_r_1887_, 4);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_r_1887_, 3);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_r_1887_, 0);
lean_dec(v_unused_2038_);
v___x_2027_ = v_r_1887_;
v_isShared_2028_ = v_isSharedCheck_2035_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_v_2025_);
lean_inc(v_k_2024_);
lean_dec(v_r_1887_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2035_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = lean_unsigned_to_nat(3u);
v___x_2030_ = lean_unsigned_to_nat(1u);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 4, v_l_1977_);
lean_ctor_set(v___x_2027_, 2, v_v_1885_);
lean_ctor_set(v___x_2027_, 1, v_k_1884_);
lean_ctor_set(v___x_2027_, 0, v___x_2030_);
v___x_2032_ = v___x_2027_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_l_1977_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_l_1977_);
v___x_2032_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2029_);
lean_ctor_set(v___x_2033_, 1, v_k_2024_);
lean_ctor_set(v___x_2033_, 2, v_v_2025_);
lean_ctor_set(v___x_2033_, 3, v___x_2032_);
lean_ctor_set(v___x_2033_, 4, v_r_2023_);
return v___x_2033_;
}
}
}
else
{
lean_object* v_size_2039_; lean_object* v_k_2040_; lean_object* v_v_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2050_; 
v_size_2039_ = lean_ctor_get(v_r_1887_, 0);
v_k_2040_ = lean_ctor_get(v_r_1887_, 1);
v_v_2041_ = lean_ctor_get(v_r_1887_, 2);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_r_1887_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2051_ = lean_ctor_get(v_r_1887_, 4);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_r_1887_, 3);
lean_dec(v_unused_2052_);
v___x_2043_ = v_r_1887_;
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_v_2041_);
lean_inc(v_k_2040_);
lean_inc(v_size_2039_);
lean_dec(v_r_1887_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 3, v_r_2023_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_size_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_2041_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_r_2023_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_r_2023_);
v___x_2046_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(2u);
v___x_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v_k_1884_);
lean_ctor_set(v___x_2048_, 2, v_v_1885_);
lean_ctor_set(v___x_2048_, 3, v_r_2023_);
lean_ctor_set(v___x_2048_, 4, v___x_2046_);
return v___x_2048_;
}
}
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_unsigned_to_nat(1u);
v___x_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v_k_1884_);
lean_ctor_set(v___x_2054_, 2, v_v_1885_);
lean_ctor_set(v___x_2054_, 3, v_r_1887_);
lean_ctor_set(v___x_2054_, 4, v_r_1887_);
return v___x_2054_;
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2057_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
v___x_2058_ = lean_unsigned_to_nat(35u);
v___x_2059_ = lean_unsigned_to_nat(276u);
v___x_2060_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
v___x_2061_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2062_ = l_mkPanicMessageWithDecl(v___x_2061_, v___x_2060_, v___x_2059_, v___x_2058_, v___x_2057_);
return v___x_2062_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2063_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
v___x_2064_ = lean_unsigned_to_nat(21u);
v___x_2065_ = lean_unsigned_to_nat(277u);
v___x_2066_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
v___x_2067_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2068_ = l_mkPanicMessageWithDecl(v___x_2067_, v___x_2066_, v___x_2065_, v___x_2064_, v___x_2063_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg(lean_object* v_k_2069_, lean_object* v_v_2070_, lean_object* v_l_2071_, lean_object* v_r_2072_){
_start:
{
if (lean_obj_tag(v_l_2071_) == 0)
{
if (lean_obj_tag(v_r_2072_) == 0)
{
lean_object* v_size_2073_; lean_object* v_size_2074_; lean_object* v_k_2075_; lean_object* v_v_2076_; lean_object* v_l_2077_; lean_object* v_r_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v_size_2073_ = lean_ctor_get(v_l_2071_, 0);
v_size_2074_ = lean_ctor_get(v_r_2072_, 0);
v_k_2075_ = lean_ctor_get(v_r_2072_, 1);
v_v_2076_ = lean_ctor_get(v_r_2072_, 2);
v_l_2077_ = lean_ctor_get(v_r_2072_, 3);
lean_inc(v_l_2077_);
v_r_2078_ = lean_ctor_get(v_r_2072_, 4);
v___x_2079_ = lean_unsigned_to_nat(3u);
v___x_2080_ = lean_nat_mul(v___x_2079_, v_size_2073_);
v___x_2081_ = lean_nat_dec_lt(v___x_2080_, v_size_2074_);
lean_dec(v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec(v_l_2077_);
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = lean_nat_add(v___x_2082_, v_size_2073_);
v___x_2084_ = lean_nat_add(v___x_2083_, v_size_2074_);
lean_dec(v___x_2083_);
v___x_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v_k_2069_);
lean_ctor_set(v___x_2085_, 2, v_v_2070_);
lean_ctor_set(v___x_2085_, 3, v_l_2071_);
lean_ctor_set(v___x_2085_, 4, v_r_2072_);
return v___x_2085_;
}
else
{
lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2155_; 
lean_inc(v_r_2078_);
lean_inc(v_v_2076_);
lean_inc(v_k_2075_);
lean_inc(v_size_2074_);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_r_2072_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; 
v_unused_2156_ = lean_ctor_get(v_r_2072_, 4);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_r_2072_, 3);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_r_2072_, 2);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_r_2072_, 1);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_r_2072_, 0);
lean_dec(v_unused_2160_);
v___x_2087_ = v_r_2072_;
v_isShared_2088_ = v_isSharedCheck_2155_;
goto v_resetjp_2086_;
}
else
{
lean_dec(v_r_2072_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2155_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
if (lean_obj_tag(v_l_2077_) == 0)
{
if (lean_obj_tag(v_r_2078_) == 0)
{
lean_object* v_size_2089_; lean_object* v_k_2090_; lean_object* v_v_2091_; lean_object* v_l_2092_; lean_object* v_r_2093_; lean_object* v_size_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_size_2089_ = lean_ctor_get(v_l_2077_, 0);
v_k_2090_ = lean_ctor_get(v_l_2077_, 1);
v_v_2091_ = lean_ctor_get(v_l_2077_, 2);
v_l_2092_ = lean_ctor_get(v_l_2077_, 3);
v_r_2093_ = lean_ctor_get(v_l_2077_, 4);
v_size_2094_ = lean_ctor_get(v_r_2078_, 0);
v___x_2095_ = lean_unsigned_to_nat(2u);
v___x_2096_ = lean_nat_mul(v___x_2095_, v_size_2094_);
v___x_2097_ = lean_nat_dec_lt(v_size_2089_, v___x_2096_);
lean_dec(v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2124_; 
lean_inc(v_r_2093_);
lean_inc(v_l_2092_);
lean_inc(v_v_2091_);
lean_inc(v_k_2090_);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_l_2077_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; lean_object* v_unused_2126_; lean_object* v_unused_2127_; lean_object* v_unused_2128_; lean_object* v_unused_2129_; 
v_unused_2125_ = lean_ctor_get(v_l_2077_, 4);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_l_2077_, 3);
lean_dec(v_unused_2126_);
v_unused_2127_ = lean_ctor_get(v_l_2077_, 2);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_l_2077_, 1);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_l_2077_, 0);
lean_dec(v_unused_2129_);
v___x_2099_ = v_l_2077_;
v_isShared_2100_ = v_isSharedCheck_2124_;
goto v_resetjp_2098_;
}
else
{
lean_dec(v_l_2077_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2124_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2116_; 
v___x_2101_ = lean_unsigned_to_nat(1u);
v___x_2102_ = lean_nat_add(v___x_2101_, v_size_2073_);
v___x_2103_ = lean_nat_add(v___x_2102_, v_size_2074_);
lean_dec(v_size_2074_);
if (lean_obj_tag(v_l_2092_) == 0)
{
lean_object* v_size_2122_; 
v_size_2122_ = lean_ctor_get(v_l_2092_, 0);
lean_inc(v_size_2122_);
v___y_2116_ = v_size_2122_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___y_2116_ = v___x_2123_;
goto v___jp_2115_;
}
v___jp_2104_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_nat_add(v___y_2105_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec(v___y_2105_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_r_2078_);
lean_ctor_set(v___x_2099_, 3, v_r_2093_);
lean_ctor_set(v___x_2099_, 2, v_v_2076_);
lean_ctor_set(v___x_2099_, 1, v_k_2075_);
lean_ctor_set(v___x_2099_, 0, v___x_2108_);
v___x_2110_ = v___x_2099_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_k_2075_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_v_2076_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_r_2093_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_r_2078_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 4, v___x_2110_);
lean_ctor_set(v___x_2087_, 3, v___y_2106_);
lean_ctor_set(v___x_2087_, 2, v_v_2091_);
lean_ctor_set(v___x_2087_, 1, v_k_2090_);
lean_ctor_set(v___x_2087_, 0, v___x_2103_);
v___x_2112_ = v___x_2087_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_2090_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_2091_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v___y_2106_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
v___jp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_nat_add(v___x_2102_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec(v___x_2102_);
v___x_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_k_2069_);
lean_ctor_set(v___x_2118_, 2, v_v_2070_);
lean_ctor_set(v___x_2118_, 3, v_l_2071_);
lean_ctor_set(v___x_2118_, 4, v_l_2092_);
v___x_2119_ = lean_nat_add(v___x_2101_, v_size_2094_);
if (lean_obj_tag(v_r_2093_) == 0)
{
lean_object* v_size_2120_; 
v_size_2120_ = lean_ctor_get(v_r_2093_, 0);
lean_inc(v_size_2120_);
v___y_2105_ = v___x_2119_;
v___y_2106_ = v___x_2118_;
v___y_2107_ = v_size_2120_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v___y_2105_ = v___x_2119_;
v___y_2106_ = v___x_2118_;
v___y_2107_ = v___x_2121_;
goto v___jp_2104_;
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_add(v___x_2130_, v_size_2073_);
v___x_2132_ = lean_nat_add(v___x_2131_, v_size_2074_);
lean_dec(v_size_2074_);
v___x_2133_ = lean_nat_add(v___x_2131_, v_size_2089_);
lean_dec(v___x_2131_);
lean_inc_ref(v_l_2071_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 4, v_l_2077_);
lean_ctor_set(v___x_2087_, 3, v_l_2071_);
lean_ctor_set(v___x_2087_, 2, v_v_2070_);
lean_ctor_set(v___x_2087_, 1, v_k_2069_);
lean_ctor_set(v___x_2087_, 0, v___x_2133_);
v___x_2135_ = v___x_2087_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_l_2071_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_l_2077_);
v___x_2135_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_isSharedCheck_2142_ = !lean_is_exclusive(v_l_2071_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; lean_object* v_unused_2144_; lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; 
v_unused_2143_ = lean_ctor_get(v_l_2071_, 4);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_l_2071_, 3);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_l_2071_, 2);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_l_2071_, 1);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_l_2071_, 0);
lean_dec(v_unused_2147_);
v___x_2137_ = v_l_2071_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_dec(v_l_2071_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 4, v_r_2078_);
lean_ctor_set(v___x_2137_, 3, v___x_2135_);
lean_ctor_set(v___x_2137_, 2, v_v_2076_);
lean_ctor_set(v___x_2137_, 1, v_k_2075_);
lean_ctor_set(v___x_2137_, 0, v___x_2132_);
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_k_2075_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_v_2076_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_r_2078_);
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
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_l_2077_);
lean_del_object(v___x_2087_);
lean_dec(v_v_2076_);
lean_dec(v_k_2075_);
lean_dec(v_size_2074_);
lean_dec_ref(v_l_2071_);
lean_dec(v_v_2070_);
lean_dec(v_k_2069_);
v___x_2149_ = lean_box(1);
v___x_2150_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
v___x_2151_ = l_panic___redArg(v___x_2149_, v___x_2150_);
return v___x_2151_;
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_del_object(v___x_2087_);
lean_dec(v_r_2078_);
lean_dec(v_v_2076_);
lean_dec(v_k_2075_);
lean_dec(v_size_2074_);
lean_dec_ref(v_l_2071_);
lean_dec(v_v_2070_);
lean_dec(v_k_2069_);
v___x_2152_ = lean_box(1);
v___x_2153_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
v___x_2154_ = l_panic___redArg(v___x_2152_, v___x_2153_);
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_size_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_size_2161_ = lean_ctor_get(v_l_2071_, 0);
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_nat_add(v___x_2162_, v_size_2161_);
v___x_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v_k_2069_);
lean_ctor_set(v___x_2164_, 2, v_v_2070_);
lean_ctor_set(v___x_2164_, 3, v_l_2071_);
lean_ctor_set(v___x_2164_, 4, v_r_2072_);
return v___x_2164_;
}
}
else
{
if (lean_obj_tag(v_r_2072_) == 0)
{
lean_object* v_l_2165_; 
v_l_2165_ = lean_ctor_get(v_r_2072_, 3);
lean_inc(v_l_2165_);
if (lean_obj_tag(v_l_2165_) == 0)
{
lean_object* v_r_2166_; 
v_r_2166_ = lean_ctor_get(v_r_2072_, 4);
lean_inc(v_r_2166_);
if (lean_obj_tag(v_r_2166_) == 0)
{
lean_object* v_size_2167_; lean_object* v_k_2168_; lean_object* v_v_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2181_; 
v_size_2167_ = lean_ctor_get(v_r_2072_, 0);
v_k_2168_ = lean_ctor_get(v_r_2072_, 1);
v_v_2169_ = lean_ctor_get(v_r_2072_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_r_2072_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; 
v_unused_2182_ = lean_ctor_get(v_r_2072_, 4);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_r_2072_, 3);
lean_dec(v_unused_2183_);
v___x_2171_ = v_r_2072_;
v_isShared_2172_ = v_isSharedCheck_2181_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_v_2169_);
lean_inc(v_k_2168_);
lean_inc(v_size_2167_);
lean_dec(v_r_2072_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2181_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_size_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
v_size_2173_ = lean_ctor_get(v_l_2165_, 0);
v___x_2174_ = lean_unsigned_to_nat(1u);
v___x_2175_ = lean_nat_add(v___x_2174_, v_size_2167_);
lean_dec(v_size_2167_);
v___x_2176_ = lean_nat_add(v___x_2174_, v_size_2173_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 4, v_l_2165_);
lean_ctor_set(v___x_2171_, 3, v_l_2071_);
lean_ctor_set(v___x_2171_, 2, v_v_2070_);
lean_ctor_set(v___x_2171_, 1, v_k_2069_);
lean_ctor_set(v___x_2171_, 0, v___x_2176_);
v___x_2178_ = v___x_2171_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_l_2071_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_l_2165_);
v___x_2178_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2175_);
lean_ctor_set(v___x_2179_, 1, v_k_2168_);
lean_ctor_set(v___x_2179_, 2, v_v_2169_);
lean_ctor_set(v___x_2179_, 3, v___x_2178_);
lean_ctor_set(v___x_2179_, 4, v_r_2166_);
return v___x_2179_;
}
}
}
else
{
lean_object* v_k_2184_; lean_object* v_v_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2207_; 
v_k_2184_ = lean_ctor_get(v_r_2072_, 1);
v_v_2185_ = lean_ctor_get(v_r_2072_, 2);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_r_2072_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2208_ = lean_ctor_get(v_r_2072_, 4);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_r_2072_, 3);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_r_2072_, 0);
lean_dec(v_unused_2210_);
v___x_2187_ = v_r_2072_;
v_isShared_2188_ = v_isSharedCheck_2207_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_v_2185_);
lean_inc(v_k_2184_);
lean_dec(v_r_2072_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2207_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v_k_2189_; lean_object* v_v_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2203_; 
v_k_2189_ = lean_ctor_get(v_l_2165_, 1);
v_v_2190_ = lean_ctor_get(v_l_2165_, 2);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_l_2165_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; lean_object* v_unused_2205_; lean_object* v_unused_2206_; 
v_unused_2204_ = lean_ctor_get(v_l_2165_, 4);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_l_2165_, 3);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_l_2165_, 0);
lean_dec(v_unused_2206_);
v___x_2192_ = v_l_2165_;
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_v_2190_);
lean_inc(v_k_2189_);
lean_dec(v_l_2165_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2194_ = lean_unsigned_to_nat(3u);
v___x_2195_ = lean_unsigned_to_nat(1u);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 4, v_r_2166_);
lean_ctor_set(v___x_2192_, 3, v_r_2166_);
lean_ctor_set(v___x_2192_, 2, v_v_2070_);
lean_ctor_set(v___x_2192_, 1, v_k_2069_);
lean_ctor_set(v___x_2192_, 0, v___x_2195_);
v___x_2197_ = v___x_2192_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_r_2166_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_r_2166_);
v___x_2197_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 3, v_r_2166_);
lean_ctor_set(v___x_2187_, 0, v___x_2195_);
v___x_2199_ = v___x_2187_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2184_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2185_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_2166_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_r_2166_);
v___x_2199_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2194_);
lean_ctor_set(v___x_2200_, 1, v_k_2189_);
lean_ctor_set(v___x_2200_, 2, v_v_2190_);
lean_ctor_set(v___x_2200_, 3, v___x_2197_);
lean_ctor_set(v___x_2200_, 4, v___x_2199_);
return v___x_2200_;
}
}
}
}
}
}
else
{
lean_object* v_r_2211_; 
v_r_2211_ = lean_ctor_get(v_r_2072_, 4);
lean_inc(v_r_2211_);
if (lean_obj_tag(v_r_2211_) == 0)
{
lean_object* v_k_2212_; lean_object* v_v_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2223_; 
v_k_2212_ = lean_ctor_get(v_r_2072_, 1);
v_v_2213_ = lean_ctor_get(v_r_2072_, 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_r_2072_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; lean_object* v_unused_2225_; lean_object* v_unused_2226_; 
v_unused_2224_ = lean_ctor_get(v_r_2072_, 4);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_r_2072_, 3);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_r_2072_, 0);
lean_dec(v_unused_2226_);
v___x_2215_ = v_r_2072_;
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_v_2213_);
lean_inc(v_k_2212_);
lean_dec(v_r_2072_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2217_ = lean_unsigned_to_nat(3u);
v___x_2218_ = lean_unsigned_to_nat(1u);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 4, v_l_2165_);
lean_ctor_set(v___x_2215_, 2, v_v_2070_);
lean_ctor_set(v___x_2215_, 1, v_k_2069_);
lean_ctor_set(v___x_2215_, 0, v___x_2218_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_l_2165_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_l_2165_);
v___x_2220_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2217_);
lean_ctor_set(v___x_2221_, 1, v_k_2212_);
lean_ctor_set(v___x_2221_, 2, v_v_2213_);
lean_ctor_set(v___x_2221_, 3, v___x_2220_);
lean_ctor_set(v___x_2221_, 4, v_r_2211_);
return v___x_2221_;
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_unsigned_to_nat(2u);
v___x_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v_k_2069_);
lean_ctor_set(v___x_2228_, 2, v_v_2070_);
lean_ctor_set(v___x_2228_, 3, v_r_2211_);
lean_ctor_set(v___x_2228_, 4, v_r_2072_);
return v___x_2228_;
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v_k_2069_);
lean_ctor_set(v___x_2230_, 2, v_v_2070_);
lean_ctor_set(v___x_2230_, 3, v_r_2072_);
lean_ctor_set(v___x_2230_, 4, v_r_2072_);
return v___x_2230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21(lean_object* v_00_u03b1_2231_, lean_object* v_00_u03b2_2232_, lean_object* v_k_2233_, lean_object* v_v_2234_, lean_object* v_l_2235_, lean_object* v_r_2236_){
_start:
{
if (lean_obj_tag(v_l_2235_) == 0)
{
if (lean_obj_tag(v_r_2236_) == 0)
{
lean_object* v_size_2237_; lean_object* v_size_2238_; lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v_l_2241_; lean_object* v_r_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_size_2237_ = lean_ctor_get(v_l_2235_, 0);
v_size_2238_ = lean_ctor_get(v_r_2236_, 0);
v_k_2239_ = lean_ctor_get(v_r_2236_, 1);
v_v_2240_ = lean_ctor_get(v_r_2236_, 2);
v_l_2241_ = lean_ctor_get(v_r_2236_, 3);
lean_inc(v_l_2241_);
v_r_2242_ = lean_ctor_get(v_r_2236_, 4);
v___x_2243_ = lean_unsigned_to_nat(3u);
v___x_2244_ = lean_nat_mul(v___x_2243_, v_size_2237_);
v___x_2245_ = lean_nat_dec_lt(v___x_2244_, v_size_2238_);
lean_dec(v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec(v_l_2241_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_add(v___x_2246_, v_size_2237_);
v___x_2248_ = lean_nat_add(v___x_2247_, v_size_2238_);
lean_dec(v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v_k_2233_);
lean_ctor_set(v___x_2249_, 2, v_v_2234_);
lean_ctor_set(v___x_2249_, 3, v_l_2235_);
lean_ctor_set(v___x_2249_, 4, v_r_2236_);
return v___x_2249_;
}
else
{
lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2319_; 
lean_inc(v_r_2242_);
lean_inc(v_v_2240_);
lean_inc(v_k_2239_);
lean_inc(v_size_2238_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_r_2236_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2320_ = lean_ctor_get(v_r_2236_, 4);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_r_2236_, 3);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_r_2236_, 2);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_r_2236_, 1);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_r_2236_, 0);
lean_dec(v_unused_2324_);
v___x_2251_ = v_r_2236_;
v_isShared_2252_ = v_isSharedCheck_2319_;
goto v_resetjp_2250_;
}
else
{
lean_dec(v_r_2236_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2319_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
if (lean_obj_tag(v_l_2241_) == 0)
{
if (lean_obj_tag(v_r_2242_) == 0)
{
lean_object* v_size_2253_; lean_object* v_k_2254_; lean_object* v_v_2255_; lean_object* v_l_2256_; lean_object* v_r_2257_; lean_object* v_size_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v_size_2253_ = lean_ctor_get(v_l_2241_, 0);
v_k_2254_ = lean_ctor_get(v_l_2241_, 1);
v_v_2255_ = lean_ctor_get(v_l_2241_, 2);
v_l_2256_ = lean_ctor_get(v_l_2241_, 3);
v_r_2257_ = lean_ctor_get(v_l_2241_, 4);
v_size_2258_ = lean_ctor_get(v_r_2242_, 0);
v___x_2259_ = lean_unsigned_to_nat(2u);
v___x_2260_ = lean_nat_mul(v___x_2259_, v_size_2258_);
v___x_2261_ = lean_nat_dec_lt(v_size_2253_, v___x_2260_);
lean_dec(v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2288_; 
lean_inc(v_r_2257_);
lean_inc(v_l_2256_);
lean_inc(v_v_2255_);
lean_inc(v_k_2254_);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; lean_object* v_unused_2290_; lean_object* v_unused_2291_; lean_object* v_unused_2292_; lean_object* v_unused_2293_; 
v_unused_2289_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_l_2241_, 2);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_l_2241_, 1);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2293_);
v___x_2263_ = v_l_2241_;
v_isShared_2264_ = v_isSharedCheck_2288_;
goto v_resetjp_2262_;
}
else
{
lean_dec(v_l_2241_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2288_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2280_; 
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = lean_nat_add(v___x_2265_, v_size_2237_);
v___x_2267_ = lean_nat_add(v___x_2266_, v_size_2238_);
lean_dec(v_size_2238_);
if (lean_obj_tag(v_l_2256_) == 0)
{
lean_object* v_size_2286_; 
v_size_2286_ = lean_ctor_get(v_l_2256_, 0);
lean_inc(v_size_2286_);
v___y_2280_ = v_size_2286_;
goto v___jp_2279_;
}
else
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_unsigned_to_nat(0u);
v___y_2280_ = v___x_2287_;
goto v___jp_2279_;
}
v___jp_2268_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_nat_add(v___y_2269_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec(v___y_2269_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 4, v_r_2242_);
lean_ctor_set(v___x_2263_, 3, v_r_2257_);
lean_ctor_set(v___x_2263_, 2, v_v_2240_);
lean_ctor_set(v___x_2263_, 1, v_k_2239_);
lean_ctor_set(v___x_2263_, 0, v___x_2272_);
v___x_2274_ = v___x_2263_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2278_, 3, v_r_2257_);
lean_ctor_set(v_reuseFailAlloc_2278_, 4, v_r_2242_);
v___x_2274_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 4, v___x_2274_);
lean_ctor_set(v___x_2251_, 3, v___y_2270_);
lean_ctor_set(v___x_2251_, 2, v_v_2255_);
lean_ctor_set(v___x_2251_, 1, v_k_2254_);
lean_ctor_set(v___x_2251_, 0, v___x_2267_);
v___x_2276_ = v___x_2251_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_k_2254_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_v_2255_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v___y_2270_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
v___jp_2279_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_nat_add(v___x_2266_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec(v___x_2266_);
v___x_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v_k_2233_);
lean_ctor_set(v___x_2282_, 2, v_v_2234_);
lean_ctor_set(v___x_2282_, 3, v_l_2235_);
lean_ctor_set(v___x_2282_, 4, v_l_2256_);
v___x_2283_ = lean_nat_add(v___x_2265_, v_size_2258_);
if (lean_obj_tag(v_r_2257_) == 0)
{
lean_object* v_size_2284_; 
v_size_2284_ = lean_ctor_get(v_r_2257_, 0);
lean_inc(v_size_2284_);
v___y_2269_ = v___x_2283_;
v___y_2270_ = v___x_2282_;
v___y_2271_ = v_size_2284_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_unsigned_to_nat(0u);
v___y_2269_ = v___x_2283_;
v___y_2270_ = v___x_2282_;
v___y_2271_ = v___x_2285_;
goto v___jp_2268_;
}
}
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2294_ = lean_unsigned_to_nat(1u);
v___x_2295_ = lean_nat_add(v___x_2294_, v_size_2237_);
v___x_2296_ = lean_nat_add(v___x_2295_, v_size_2238_);
lean_dec(v_size_2238_);
v___x_2297_ = lean_nat_add(v___x_2295_, v_size_2253_);
lean_dec(v___x_2295_);
lean_inc_ref(v_l_2235_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 4, v_l_2241_);
lean_ctor_set(v___x_2251_, 3, v_l_2235_);
lean_ctor_set(v___x_2251_, 2, v_v_2234_);
lean_ctor_set(v___x_2251_, 1, v_k_2233_);
lean_ctor_set(v___x_2251_, 0, v___x_2297_);
v___x_2299_ = v___x_2251_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_l_2235_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_l_2241_);
v___x_2299_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_isSharedCheck_2306_ = !lean_is_exclusive(v_l_2235_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; lean_object* v_unused_2308_; lean_object* v_unused_2309_; lean_object* v_unused_2310_; lean_object* v_unused_2311_; 
v_unused_2307_ = lean_ctor_get(v_l_2235_, 4);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_l_2235_, 3);
lean_dec(v_unused_2308_);
v_unused_2309_ = lean_ctor_get(v_l_2235_, 2);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_l_2235_, 1);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_l_2235_, 0);
lean_dec(v_unused_2311_);
v___x_2301_ = v_l_2235_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v_l_2235_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_r_2242_);
lean_ctor_set(v___x_2301_, 3, v___x_2299_);
lean_ctor_set(v___x_2301_, 2, v_v_2240_);
lean_ctor_set(v___x_2301_, 1, v_k_2239_);
lean_ctor_set(v___x_2301_, 0, v___x_2296_);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v_r_2242_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v_l_2241_);
lean_del_object(v___x_2251_);
lean_dec(v_v_2240_);
lean_dec(v_k_2239_);
lean_dec(v_size_2238_);
lean_dec_ref(v_l_2235_);
lean_dec(v_v_2234_);
lean_dec(v_k_2233_);
v___x_2313_ = lean_box(1);
v___x_2314_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
v___x_2315_ = l_panic___redArg(v___x_2313_, v___x_2314_);
return v___x_2315_;
}
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_del_object(v___x_2251_);
lean_dec(v_r_2242_);
lean_dec(v_v_2240_);
lean_dec(v_k_2239_);
lean_dec(v_size_2238_);
lean_dec_ref(v_l_2235_);
lean_dec(v_v_2234_);
lean_dec(v_k_2233_);
v___x_2316_ = lean_box(1);
v___x_2317_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
v___x_2318_ = l_panic___redArg(v___x_2316_, v___x_2317_);
return v___x_2318_;
}
}
}
}
else
{
lean_object* v_size_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_size_2325_ = lean_ctor_get(v_l_2235_, 0);
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_add(v___x_2326_, v_size_2325_);
v___x_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v_k_2233_);
lean_ctor_set(v___x_2328_, 2, v_v_2234_);
lean_ctor_set(v___x_2328_, 3, v_l_2235_);
lean_ctor_set(v___x_2328_, 4, v_r_2236_);
return v___x_2328_;
}
}
else
{
if (lean_obj_tag(v_r_2236_) == 0)
{
lean_object* v_l_2329_; 
v_l_2329_ = lean_ctor_get(v_r_2236_, 3);
lean_inc(v_l_2329_);
if (lean_obj_tag(v_l_2329_) == 0)
{
lean_object* v_r_2330_; 
v_r_2330_ = lean_ctor_get(v_r_2236_, 4);
lean_inc(v_r_2330_);
if (lean_obj_tag(v_r_2330_) == 0)
{
lean_object* v_size_2331_; lean_object* v_k_2332_; lean_object* v_v_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2345_; 
v_size_2331_ = lean_ctor_get(v_r_2236_, 0);
v_k_2332_ = lean_ctor_get(v_r_2236_, 1);
v_v_2333_ = lean_ctor_get(v_r_2236_, 2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_r_2236_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; lean_object* v_unused_2347_; 
v_unused_2346_ = lean_ctor_get(v_r_2236_, 4);
lean_dec(v_unused_2346_);
v_unused_2347_ = lean_ctor_get(v_r_2236_, 3);
lean_dec(v_unused_2347_);
v___x_2335_ = v_r_2236_;
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_v_2333_);
lean_inc(v_k_2332_);
lean_inc(v_size_2331_);
lean_dec(v_r_2236_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v_size_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v_size_2337_ = lean_ctor_get(v_l_2329_, 0);
v___x_2338_ = lean_unsigned_to_nat(1u);
v___x_2339_ = lean_nat_add(v___x_2338_, v_size_2331_);
lean_dec(v_size_2331_);
v___x_2340_ = lean_nat_add(v___x_2338_, v_size_2337_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 4, v_l_2329_);
lean_ctor_set(v___x_2335_, 3, v_l_2235_);
lean_ctor_set(v___x_2335_, 2, v_v_2234_);
lean_ctor_set(v___x_2335_, 1, v_k_2233_);
lean_ctor_set(v___x_2335_, 0, v___x_2340_);
v___x_2342_ = v___x_2335_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_l_2235_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v_l_2329_);
v___x_2342_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2339_);
lean_ctor_set(v___x_2343_, 1, v_k_2332_);
lean_ctor_set(v___x_2343_, 2, v_v_2333_);
lean_ctor_set(v___x_2343_, 3, v___x_2342_);
lean_ctor_set(v___x_2343_, 4, v_r_2330_);
return v___x_2343_;
}
}
}
else
{
lean_object* v_k_2348_; lean_object* v_v_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2371_; 
v_k_2348_ = lean_ctor_get(v_r_2236_, 1);
v_v_2349_ = lean_ctor_get(v_r_2236_, 2);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_r_2236_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; lean_object* v_unused_2373_; lean_object* v_unused_2374_; 
v_unused_2372_ = lean_ctor_get(v_r_2236_, 4);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_r_2236_, 3);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_r_2236_, 0);
lean_dec(v_unused_2374_);
v___x_2351_ = v_r_2236_;
v_isShared_2352_ = v_isSharedCheck_2371_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_v_2349_);
lean_inc(v_k_2348_);
lean_dec(v_r_2236_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2371_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_k_2353_; lean_object* v_v_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2367_; 
v_k_2353_ = lean_ctor_get(v_l_2329_, 1);
v_v_2354_ = lean_ctor_get(v_l_2329_, 2);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_l_2329_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; lean_object* v_unused_2369_; lean_object* v_unused_2370_; 
v_unused_2368_ = lean_ctor_get(v_l_2329_, 4);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_l_2329_, 3);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_l_2329_, 0);
lean_dec(v_unused_2370_);
v___x_2356_ = v_l_2329_;
v_isShared_2357_ = v_isSharedCheck_2367_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_v_2354_);
lean_inc(v_k_2353_);
lean_dec(v_l_2329_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2367_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2358_ = lean_unsigned_to_nat(3u);
v___x_2359_ = lean_unsigned_to_nat(1u);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 4, v_r_2330_);
lean_ctor_set(v___x_2356_, 3, v_r_2330_);
lean_ctor_set(v___x_2356_, 2, v_v_2234_);
lean_ctor_set(v___x_2356_, 1, v_k_2233_);
lean_ctor_set(v___x_2356_, 0, v___x_2359_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_r_2330_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v_r_2330_);
v___x_2361_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 3, v_r_2330_);
lean_ctor_set(v___x_2351_, 0, v___x_2359_);
v___x_2363_ = v___x_2351_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_2348_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_2349_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_r_2330_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_r_2330_);
v___x_2363_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2358_);
lean_ctor_set(v___x_2364_, 1, v_k_2353_);
lean_ctor_set(v___x_2364_, 2, v_v_2354_);
lean_ctor_set(v___x_2364_, 3, v___x_2361_);
lean_ctor_set(v___x_2364_, 4, v___x_2363_);
return v___x_2364_;
}
}
}
}
}
}
else
{
lean_object* v_r_2375_; 
v_r_2375_ = lean_ctor_get(v_r_2236_, 4);
lean_inc(v_r_2375_);
if (lean_obj_tag(v_r_2375_) == 0)
{
lean_object* v_k_2376_; lean_object* v_v_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2387_; 
v_k_2376_ = lean_ctor_get(v_r_2236_, 1);
v_v_2377_ = lean_ctor_get(v_r_2236_, 2);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_r_2236_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; lean_object* v_unused_2389_; lean_object* v_unused_2390_; 
v_unused_2388_ = lean_ctor_get(v_r_2236_, 4);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_r_2236_, 3);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_r_2236_, 0);
lean_dec(v_unused_2390_);
v___x_2379_ = v_r_2236_;
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_v_2377_);
lean_inc(v_k_2376_);
lean_dec(v_r_2236_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2381_ = lean_unsigned_to_nat(3u);
v___x_2382_ = lean_unsigned_to_nat(1u);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 4, v_l_2329_);
lean_ctor_set(v___x_2379_, 2, v_v_2234_);
lean_ctor_set(v___x_2379_, 1, v_k_2233_);
lean_ctor_set(v___x_2379_, 0, v___x_2382_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2386_, 3, v_l_2329_);
lean_ctor_set(v_reuseFailAlloc_2386_, 4, v_l_2329_);
v___x_2384_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2381_);
lean_ctor_set(v___x_2385_, 1, v_k_2376_);
lean_ctor_set(v___x_2385_, 2, v_v_2377_);
lean_ctor_set(v___x_2385_, 3, v___x_2384_);
lean_ctor_set(v___x_2385_, 4, v_r_2375_);
return v___x_2385_;
}
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_unsigned_to_nat(2u);
v___x_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v_k_2233_);
lean_ctor_set(v___x_2392_, 2, v_v_2234_);
lean_ctor_set(v___x_2392_, 3, v_r_2375_);
lean_ctor_set(v___x_2392_, 4, v_r_2236_);
return v___x_2392_;
}
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_unsigned_to_nat(1u);
v___x_2394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v_k_2233_);
lean_ctor_set(v___x_2394_, 2, v_v_2234_);
lean_ctor_set(v___x_2394_, 3, v_r_2236_);
lean_ctor_set(v___x_2394_, 4, v_r_2236_);
return v___x_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object* v_k_2395_, lean_object* v_v_2396_, lean_object* v_l_2397_, lean_object* v_r_2398_){
_start:
{
if (lean_obj_tag(v_l_2397_) == 0)
{
if (lean_obj_tag(v_r_2398_) == 0)
{
lean_object* v_size_2399_; lean_object* v_k_2400_; lean_object* v_v_2401_; lean_object* v_l_2402_; lean_object* v_r_2403_; lean_object* v_size_2404_; lean_object* v_k_2405_; lean_object* v_v_2406_; lean_object* v_l_2407_; lean_object* v_r_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v_size_2399_ = lean_ctor_get(v_l_2397_, 0);
v_k_2400_ = lean_ctor_get(v_l_2397_, 1);
v_v_2401_ = lean_ctor_get(v_l_2397_, 2);
v_l_2402_ = lean_ctor_get(v_l_2397_, 3);
v_r_2403_ = lean_ctor_get(v_l_2397_, 4);
lean_inc(v_r_2403_);
v_size_2404_ = lean_ctor_get(v_r_2398_, 0);
v_k_2405_ = lean_ctor_get(v_r_2398_, 1);
v_v_2406_ = lean_ctor_get(v_r_2398_, 2);
v_l_2407_ = lean_ctor_get(v_r_2398_, 3);
lean_inc(v_l_2407_);
v_r_2408_ = lean_ctor_get(v_r_2398_, 4);
v___x_2409_ = lean_unsigned_to_nat(3u);
v___x_2410_ = lean_nat_mul(v___x_2409_, v_size_2399_);
v___x_2411_ = lean_nat_dec_lt(v___x_2410_, v_size_2404_);
lean_dec(v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
lean_dec(v_l_2407_);
v___x_2412_ = lean_nat_mul(v___x_2409_, v_size_2404_);
v___x_2413_ = lean_nat_dec_lt(v___x_2412_, v_size_2399_);
lean_dec(v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec(v_r_2403_);
v___x_2414_ = lean_unsigned_to_nat(1u);
v___x_2415_ = lean_nat_add(v___x_2414_, v_size_2399_);
v___x_2416_ = lean_nat_add(v___x_2415_, v_size_2404_);
lean_dec(v___x_2415_);
v___x_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v_k_2395_);
lean_ctor_set(v___x_2417_, 2, v_v_2396_);
lean_ctor_set(v___x_2417_, 3, v_l_2397_);
lean_ctor_set(v___x_2417_, 4, v_r_2398_);
return v___x_2417_;
}
else
{
lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2483_; 
lean_inc(v_l_2402_);
lean_inc(v_v_2401_);
lean_inc(v_k_2400_);
lean_inc(v_size_2399_);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_l_2397_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; lean_object* v_unused_2485_; lean_object* v_unused_2486_; lean_object* v_unused_2487_; lean_object* v_unused_2488_; 
v_unused_2484_ = lean_ctor_get(v_l_2397_, 4);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v_l_2397_, 3);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v_l_2397_, 2);
lean_dec(v_unused_2486_);
v_unused_2487_ = lean_ctor_get(v_l_2397_, 1);
lean_dec(v_unused_2487_);
v_unused_2488_ = lean_ctor_get(v_l_2397_, 0);
lean_dec(v_unused_2488_);
v___x_2419_ = v_l_2397_;
v_isShared_2420_ = v_isSharedCheck_2483_;
goto v_resetjp_2418_;
}
else
{
lean_dec(v_l_2397_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2483_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_size_2421_; lean_object* v_size_2422_; lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v_l_2425_; lean_object* v_r_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v_size_2421_ = lean_ctor_get(v_l_2402_, 0);
v_size_2422_ = lean_ctor_get(v_r_2403_, 0);
v_k_2423_ = lean_ctor_get(v_r_2403_, 1);
v_v_2424_ = lean_ctor_get(v_r_2403_, 2);
v_l_2425_ = lean_ctor_get(v_r_2403_, 3);
v_r_2426_ = lean_ctor_get(v_r_2403_, 4);
v___x_2427_ = lean_unsigned_to_nat(2u);
v___x_2428_ = lean_nat_mul(v___x_2427_, v_size_2421_);
v___x_2429_ = lean_nat_dec_lt(v_size_2422_, v___x_2428_);
lean_dec(v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2468_; 
lean_inc(v_r_2426_);
lean_inc(v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_r_2403_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; lean_object* v_unused_2470_; lean_object* v_unused_2471_; lean_object* v_unused_2472_; lean_object* v_unused_2473_; 
v_unused_2469_ = lean_ctor_get(v_r_2403_, 4);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v_r_2403_, 3);
lean_dec(v_unused_2470_);
v_unused_2471_ = lean_ctor_get(v_r_2403_, 2);
lean_dec(v_unused_2471_);
v_unused_2472_ = lean_ctor_get(v_r_2403_, 1);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v_r_2403_, 0);
lean_dec(v_unused_2473_);
v___x_2431_ = v_r_2403_;
v_isShared_2432_ = v_isSharedCheck_2468_;
goto v_resetjp_2430_;
}
else
{
lean_dec(v_r_2403_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2468_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___x_2456_; lean_object* v___y_2458_; 
v___x_2433_ = lean_unsigned_to_nat(1u);
v___x_2434_ = lean_nat_add(v___x_2433_, v_size_2399_);
lean_dec(v_size_2399_);
v___x_2435_ = lean_nat_add(v___x_2434_, v_size_2404_);
lean_dec(v___x_2434_);
v___x_2456_ = lean_nat_add(v___x_2433_, v_size_2421_);
if (lean_obj_tag(v_l_2425_) == 0)
{
lean_object* v_size_2466_; 
v_size_2466_ = lean_ctor_get(v_l_2425_, 0);
lean_inc(v_size_2466_);
v___y_2458_ = v_size_2466_;
goto v___jp_2457_;
}
else
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v___y_2458_ = v___x_2467_;
goto v___jp_2457_;
}
v___jp_2436_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2440_ = lean_nat_add(v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec(v___y_2438_);
lean_inc_ref(v_r_2398_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 4, v_r_2398_);
lean_ctor_set(v___x_2431_, 3, v_r_2426_);
lean_ctor_set(v___x_2431_, 2, v_v_2396_);
lean_ctor_set(v___x_2431_, 1, v_k_2395_);
lean_ctor_set(v___x_2431_, 0, v___x_2440_);
v___x_2442_ = v___x_2431_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_r_2426_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_r_2398_);
v___x_2442_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
v_isSharedCheck_2449_ = !lean_is_exclusive(v_r_2398_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; lean_object* v_unused_2451_; lean_object* v_unused_2452_; lean_object* v_unused_2453_; lean_object* v_unused_2454_; 
v_unused_2450_ = lean_ctor_get(v_r_2398_, 4);
lean_dec(v_unused_2450_);
v_unused_2451_ = lean_ctor_get(v_r_2398_, 3);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v_r_2398_, 2);
lean_dec(v_unused_2452_);
v_unused_2453_ = lean_ctor_get(v_r_2398_, 1);
lean_dec(v_unused_2453_);
v_unused_2454_ = lean_ctor_get(v_r_2398_, 0);
lean_dec(v_unused_2454_);
v___x_2444_ = v_r_2398_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_dec(v_r_2398_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 4, v___x_2442_);
lean_ctor_set(v___x_2444_, 3, v___y_2437_);
lean_ctor_set(v___x_2444_, 2, v_v_2424_);
lean_ctor_set(v___x_2444_, 1, v_k_2423_);
lean_ctor_set(v___x_2444_, 0, v___x_2435_);
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v___y_2437_);
lean_ctor_set(v_reuseFailAlloc_2448_, 4, v___x_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
v___jp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2459_ = lean_nat_add(v___x_2456_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec(v___x_2456_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 4, v_l_2425_);
lean_ctor_set(v___x_2419_, 0, v___x_2459_);
v___x_2461_ = v___x_2419_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_k_2400_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_v_2401_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_l_2402_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v_l_2425_);
v___x_2461_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_nat_add(v___x_2433_, v_size_2404_);
if (lean_obj_tag(v_r_2426_) == 0)
{
lean_object* v_size_2463_; 
v_size_2463_ = lean_ctor_get(v_r_2426_, 0);
lean_inc(v_size_2463_);
v___y_2437_ = v___x_2461_;
v___y_2438_ = v___x_2462_;
v___y_2439_ = v_size_2463_;
goto v___jp_2436_;
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___y_2437_ = v___x_2461_;
v___y_2438_ = v___x_2462_;
v___y_2439_ = v___x_2464_;
goto v___jp_2436_;
}
}
}
}
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2474_ = lean_unsigned_to_nat(1u);
v___x_2475_ = lean_nat_add(v___x_2474_, v_size_2399_);
lean_dec(v_size_2399_);
v___x_2476_ = lean_nat_add(v___x_2475_, v_size_2404_);
lean_dec(v___x_2475_);
v___x_2477_ = lean_nat_add(v___x_2474_, v_size_2404_);
v___x_2478_ = lean_nat_add(v___x_2477_, v_size_2422_);
lean_dec(v___x_2477_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 4, v_r_2398_);
lean_ctor_set(v___x_2419_, 3, v_r_2403_);
lean_ctor_set(v___x_2419_, 2, v_v_2396_);
lean_ctor_set(v___x_2419_, 1, v_k_2395_);
lean_ctor_set(v___x_2419_, 0, v___x_2478_);
v___x_2480_ = v___x_2419_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_r_2403_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_r_2398_);
v___x_2480_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2476_);
lean_ctor_set(v___x_2481_, 1, v_k_2400_);
lean_ctor_set(v___x_2481_, 2, v_v_2401_);
lean_ctor_set(v___x_2481_, 3, v_l_2402_);
lean_ctor_set(v___x_2481_, 4, v___x_2480_);
return v___x_2481_;
}
}
}
}
}
else
{
lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2552_; 
lean_inc(v_r_2408_);
lean_inc(v_v_2406_);
lean_inc(v_k_2405_);
lean_inc(v_size_2404_);
lean_dec(v_r_2403_);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_r_2398_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; lean_object* v_unused_2554_; lean_object* v_unused_2555_; lean_object* v_unused_2556_; lean_object* v_unused_2557_; 
v_unused_2553_ = lean_ctor_get(v_r_2398_, 4);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_r_2398_, 3);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_r_2398_, 2);
lean_dec(v_unused_2555_);
v_unused_2556_ = lean_ctor_get(v_r_2398_, 1);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_r_2398_, 0);
lean_dec(v_unused_2557_);
v___x_2490_ = v_r_2398_;
v_isShared_2491_ = v_isSharedCheck_2552_;
goto v_resetjp_2489_;
}
else
{
lean_dec(v_r_2398_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2552_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_size_2492_; lean_object* v_k_2493_; lean_object* v_v_2494_; lean_object* v_l_2495_; lean_object* v_r_2496_; lean_object* v_size_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_size_2492_ = lean_ctor_get(v_l_2407_, 0);
v_k_2493_ = lean_ctor_get(v_l_2407_, 1);
v_v_2494_ = lean_ctor_get(v_l_2407_, 2);
v_l_2495_ = lean_ctor_get(v_l_2407_, 3);
v_r_2496_ = lean_ctor_get(v_l_2407_, 4);
v_size_2497_ = lean_ctor_get(v_r_2408_, 0);
v___x_2498_ = lean_unsigned_to_nat(2u);
v___x_2499_ = lean_nat_mul(v___x_2498_, v_size_2497_);
v___x_2500_ = lean_nat_dec_lt(v_size_2492_, v___x_2499_);
lean_dec(v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2527_; 
lean_inc(v_r_2496_);
lean_inc(v_l_2495_);
lean_inc(v_v_2494_);
lean_inc(v_k_2493_);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_l_2407_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; lean_object* v_unused_2529_; lean_object* v_unused_2530_; lean_object* v_unused_2531_; lean_object* v_unused_2532_; 
v_unused_2528_ = lean_ctor_get(v_l_2407_, 4);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v_l_2407_, 3);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_l_2407_, 2);
lean_dec(v_unused_2530_);
v_unused_2531_ = lean_ctor_get(v_l_2407_, 1);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_l_2407_, 0);
lean_dec(v_unused_2532_);
v___x_2502_ = v_l_2407_;
v_isShared_2503_ = v_isSharedCheck_2527_;
goto v_resetjp_2501_;
}
else
{
lean_dec(v_l_2407_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2527_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2519_; 
v___x_2504_ = lean_unsigned_to_nat(1u);
v___x_2505_ = lean_nat_add(v___x_2504_, v_size_2399_);
v___x_2506_ = lean_nat_add(v___x_2505_, v_size_2404_);
lean_dec(v_size_2404_);
if (lean_obj_tag(v_l_2495_) == 0)
{
lean_object* v_size_2525_; 
v_size_2525_ = lean_ctor_get(v_l_2495_, 0);
lean_inc(v_size_2525_);
v___y_2519_ = v_size_2525_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_unsigned_to_nat(0u);
v___y_2519_ = v___x_2526_;
goto v___jp_2518_;
}
v___jp_2507_:
{
lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2511_ = lean_nat_add(v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec(v___y_2509_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 4, v_r_2408_);
lean_ctor_set(v___x_2502_, 3, v_r_2496_);
lean_ctor_set(v___x_2502_, 2, v_v_2406_);
lean_ctor_set(v___x_2502_, 1, v_k_2405_);
lean_ctor_set(v___x_2502_, 0, v___x_2511_);
v___x_2513_ = v___x_2502_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_k_2405_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_v_2406_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_r_2496_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_r_2408_);
v___x_2513_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2515_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 4, v___x_2513_);
lean_ctor_set(v___x_2490_, 3, v___y_2508_);
lean_ctor_set(v___x_2490_, 2, v_v_2494_);
lean_ctor_set(v___x_2490_, 1, v_k_2493_);
lean_ctor_set(v___x_2490_, 0, v___x_2506_);
v___x_2515_ = v___x_2490_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_k_2493_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_v_2494_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v___y_2508_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
v___jp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_nat_add(v___x_2505_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec(v___x_2505_);
v___x_2521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v_k_2395_);
lean_ctor_set(v___x_2521_, 2, v_v_2396_);
lean_ctor_set(v___x_2521_, 3, v_l_2397_);
lean_ctor_set(v___x_2521_, 4, v_l_2495_);
v___x_2522_ = lean_nat_add(v___x_2504_, v_size_2497_);
if (lean_obj_tag(v_r_2496_) == 0)
{
lean_object* v_size_2523_; 
v_size_2523_ = lean_ctor_get(v_r_2496_, 0);
lean_inc(v_size_2523_);
v___y_2508_ = v___x_2521_;
v___y_2509_ = v___x_2522_;
v___y_2510_ = v_size_2523_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_unsigned_to_nat(0u);
v___y_2508_ = v___x_2521_;
v___y_2509_ = v___x_2522_;
v___y_2510_ = v___x_2524_;
goto v___jp_2507_;
}
}
}
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = lean_nat_add(v___x_2533_, v_size_2399_);
v___x_2535_ = lean_nat_add(v___x_2534_, v_size_2404_);
lean_dec(v_size_2404_);
v___x_2536_ = lean_nat_add(v___x_2534_, v_size_2492_);
lean_dec(v___x_2534_);
lean_inc_ref(v_l_2397_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 4, v_l_2407_);
lean_ctor_set(v___x_2490_, 3, v_l_2397_);
lean_ctor_set(v___x_2490_, 2, v_v_2396_);
lean_ctor_set(v___x_2490_, 1, v_k_2395_);
lean_ctor_set(v___x_2490_, 0, v___x_2536_);
v___x_2538_ = v___x_2490_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v_l_2397_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_l_2407_);
v___x_2538_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_isSharedCheck_2545_ = !lean_is_exclusive(v_l_2397_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; lean_object* v_unused_2547_; lean_object* v_unused_2548_; lean_object* v_unused_2549_; lean_object* v_unused_2550_; 
v_unused_2546_ = lean_ctor_get(v_l_2397_, 4);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_l_2397_, 3);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_l_2397_, 2);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_l_2397_, 1);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_l_2397_, 0);
lean_dec(v_unused_2550_);
v___x_2540_ = v_l_2397_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_dec(v_l_2397_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 4, v_r_2408_);
lean_ctor_set(v___x_2540_, 3, v___x_2538_);
lean_ctor_set(v___x_2540_, 2, v_v_2406_);
lean_ctor_set(v___x_2540_, 1, v_k_2405_);
lean_ctor_set(v___x_2540_, 0, v___x_2535_);
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_k_2405_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_v_2406_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_r_2408_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2558_; 
v_l_2558_ = lean_ctor_get(v_l_2397_, 3);
if (lean_obj_tag(v_l_2558_) == 0)
{
lean_object* v_r_2559_; 
lean_inc_ref(v_l_2558_);
v_r_2559_ = lean_ctor_get(v_l_2397_, 4);
lean_inc(v_r_2559_);
if (lean_obj_tag(v_r_2559_) == 0)
{
lean_object* v_size_2560_; lean_object* v_k_2561_; lean_object* v_v_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2585_; 
v_size_2560_ = lean_ctor_get(v_l_2397_, 0);
v_k_2561_ = lean_ctor_get(v_l_2397_, 1);
v_v_2562_ = lean_ctor_get(v_l_2397_, 2);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_l_2397_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; lean_object* v_unused_2587_; 
v_unused_2586_ = lean_ctor_get(v_l_2397_, 4);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_l_2397_, 3);
lean_dec(v_unused_2587_);
v___x_2564_ = v_l_2397_;
v_isShared_2565_ = v_isSharedCheck_2585_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_v_2562_);
lean_inc(v_k_2561_);
lean_inc(v_size_2560_);
lean_dec(v_l_2397_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2585_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v_size_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v_size_2566_ = lean_ctor_get(v_r_2559_, 0);
v___x_2567_ = lean_unsigned_to_nat(1u);
v___x_2568_ = lean_nat_add(v___x_2567_, v_size_2560_);
lean_dec(v_size_2560_);
v___x_2569_ = lean_nat_add(v___x_2567_, v_size_2566_);
lean_inc_ref(v_r_2559_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 4, v_r_2398_);
lean_ctor_set(v___x_2564_, 3, v_r_2559_);
lean_ctor_set(v___x_2564_, 2, v_v_2396_);
lean_ctor_set(v___x_2564_, 1, v_k_2395_);
lean_ctor_set(v___x_2564_, 0, v___x_2569_);
v___x_2571_ = v___x_2564_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_r_2559_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_r_2398_);
v___x_2571_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_isSharedCheck_2578_ = !lean_is_exclusive(v_r_2559_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; lean_object* v_unused_2580_; lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; 
v_unused_2579_ = lean_ctor_get(v_r_2559_, 4);
lean_dec(v_unused_2579_);
v_unused_2580_ = lean_ctor_get(v_r_2559_, 3);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v_r_2559_, 2);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_r_2559_, 1);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_r_2559_, 0);
lean_dec(v_unused_2583_);
v___x_2573_ = v_r_2559_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v_r_2559_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 4, v___x_2571_);
lean_ctor_set(v___x_2573_, 3, v_l_2558_);
lean_ctor_set(v___x_2573_, 2, v_v_2562_);
lean_ctor_set(v___x_2573_, 1, v_k_2561_);
lean_ctor_set(v___x_2573_, 0, v___x_2568_);
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_k_2561_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_v_2562_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_l_2558_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v___x_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
else
{
lean_object* v_k_2588_; lean_object* v_v_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2599_; 
v_k_2588_ = lean_ctor_get(v_l_2397_, 1);
v_v_2589_ = lean_ctor_get(v_l_2397_, 2);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_l_2397_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; lean_object* v_unused_2601_; lean_object* v_unused_2602_; 
v_unused_2600_ = lean_ctor_get(v_l_2397_, 4);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_l_2397_, 3);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v_l_2397_, 0);
lean_dec(v_unused_2602_);
v___x_2591_ = v_l_2397_;
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_v_2589_);
lean_inc(v_k_2588_);
lean_dec(v_l_2397_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = lean_unsigned_to_nat(3u);
v___x_2594_ = lean_unsigned_to_nat(1u);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 3, v_r_2559_);
lean_ctor_set(v___x_2591_, 2, v_v_2396_);
lean_ctor_set(v___x_2591_, 1, v_k_2395_);
lean_ctor_set(v___x_2591_, 0, v___x_2594_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_r_2559_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_r_2559_);
v___x_2596_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2593_);
lean_ctor_set(v___x_2597_, 1, v_k_2588_);
lean_ctor_set(v___x_2597_, 2, v_v_2589_);
lean_ctor_set(v___x_2597_, 3, v_l_2558_);
lean_ctor_set(v___x_2597_, 4, v___x_2596_);
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_r_2603_; 
v_r_2603_ = lean_ctor_get(v_l_2397_, 4);
lean_inc(v_r_2603_);
if (lean_obj_tag(v_r_2603_) == 0)
{
lean_object* v_k_2604_; lean_object* v_v_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2627_; 
lean_inc(v_l_2558_);
v_k_2604_ = lean_ctor_get(v_l_2397_, 1);
v_v_2605_ = lean_ctor_get(v_l_2397_, 2);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_l_2397_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; lean_object* v_unused_2629_; lean_object* v_unused_2630_; 
v_unused_2628_ = lean_ctor_get(v_l_2397_, 4);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_l_2397_, 3);
lean_dec(v_unused_2629_);
v_unused_2630_ = lean_ctor_get(v_l_2397_, 0);
lean_dec(v_unused_2630_);
v___x_2607_ = v_l_2397_;
v_isShared_2608_ = v_isSharedCheck_2627_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_v_2605_);
lean_inc(v_k_2604_);
lean_dec(v_l_2397_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2627_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_k_2609_; lean_object* v_v_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2623_; 
v_k_2609_ = lean_ctor_get(v_r_2603_, 1);
v_v_2610_ = lean_ctor_get(v_r_2603_, 2);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_r_2603_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; lean_object* v_unused_2625_; lean_object* v_unused_2626_; 
v_unused_2624_ = lean_ctor_get(v_r_2603_, 4);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_r_2603_, 3);
lean_dec(v_unused_2625_);
v_unused_2626_ = lean_ctor_get(v_r_2603_, 0);
lean_dec(v_unused_2626_);
v___x_2612_ = v_r_2603_;
v_isShared_2613_ = v_isSharedCheck_2623_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_v_2610_);
lean_inc(v_k_2609_);
lean_dec(v_r_2603_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2623_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2614_ = lean_unsigned_to_nat(3u);
v___x_2615_ = lean_unsigned_to_nat(1u);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 4, v_l_2558_);
lean_ctor_set(v___x_2612_, 3, v_l_2558_);
lean_ctor_set(v___x_2612_, 2, v_v_2605_);
lean_ctor_set(v___x_2612_, 1, v_k_2604_);
lean_ctor_set(v___x_2612_, 0, v___x_2615_);
v___x_2617_ = v___x_2612_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_k_2604_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_v_2605_);
lean_ctor_set(v_reuseFailAlloc_2622_, 3, v_l_2558_);
lean_ctor_set(v_reuseFailAlloc_2622_, 4, v_l_2558_);
v___x_2617_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2619_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 4, v_l_2558_);
lean_ctor_set(v___x_2607_, 2, v_v_2396_);
lean_ctor_set(v___x_2607_, 1, v_k_2395_);
lean_ctor_set(v___x_2607_, 0, v___x_2615_);
v___x_2619_ = v___x_2607_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v_l_2558_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v_l_2558_);
v___x_2619_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2614_);
lean_ctor_set(v___x_2620_, 1, v_k_2609_);
lean_ctor_set(v___x_2620_, 2, v_v_2610_);
lean_ctor_set(v___x_2620_, 3, v___x_2617_);
lean_ctor_set(v___x_2620_, 4, v___x_2619_);
return v___x_2620_;
}
}
}
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_unsigned_to_nat(2u);
v___x_2632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
lean_ctor_set(v___x_2632_, 1, v_k_2395_);
lean_ctor_set(v___x_2632_, 2, v_v_2396_);
lean_ctor_set(v___x_2632_, 3, v_l_2397_);
lean_ctor_set(v___x_2632_, 4, v_r_2603_);
return v___x_2632_;
}
}
}
}
else
{
if (lean_obj_tag(v_r_2398_) == 0)
{
lean_object* v_l_2633_; 
v_l_2633_ = lean_ctor_get(v_r_2398_, 3);
lean_inc(v_l_2633_);
if (lean_obj_tag(v_l_2633_) == 0)
{
lean_object* v_r_2634_; 
v_r_2634_ = lean_ctor_get(v_r_2398_, 4);
lean_inc(v_r_2634_);
if (lean_obj_tag(v_r_2634_) == 0)
{
lean_object* v_size_2635_; lean_object* v_k_2636_; lean_object* v_v_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2649_; 
v_size_2635_ = lean_ctor_get(v_r_2398_, 0);
v_k_2636_ = lean_ctor_get(v_r_2398_, 1);
v_v_2637_ = lean_ctor_get(v_r_2398_, 2);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_r_2398_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; lean_object* v_unused_2651_; 
v_unused_2650_ = lean_ctor_get(v_r_2398_, 4);
lean_dec(v_unused_2650_);
v_unused_2651_ = lean_ctor_get(v_r_2398_, 3);
lean_dec(v_unused_2651_);
v___x_2639_ = v_r_2398_;
v_isShared_2640_ = v_isSharedCheck_2649_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_v_2637_);
lean_inc(v_k_2636_);
lean_inc(v_size_2635_);
lean_dec(v_r_2398_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2649_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_size_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v_size_2641_ = lean_ctor_get(v_l_2633_, 0);
v___x_2642_ = lean_unsigned_to_nat(1u);
v___x_2643_ = lean_nat_add(v___x_2642_, v_size_2635_);
lean_dec(v_size_2635_);
v___x_2644_ = lean_nat_add(v___x_2642_, v_size_2641_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 4, v_l_2633_);
lean_ctor_set(v___x_2639_, 3, v_l_2397_);
lean_ctor_set(v___x_2639_, 2, v_v_2396_);
lean_ctor_set(v___x_2639_, 1, v_k_2395_);
lean_ctor_set(v___x_2639_, 0, v___x_2644_);
v___x_2646_ = v___x_2639_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_l_2397_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_l_2633_);
v___x_2646_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2643_);
lean_ctor_set(v___x_2647_, 1, v_k_2636_);
lean_ctor_set(v___x_2647_, 2, v_v_2637_);
lean_ctor_set(v___x_2647_, 3, v___x_2646_);
lean_ctor_set(v___x_2647_, 4, v_r_2634_);
return v___x_2647_;
}
}
}
else
{
lean_object* v_k_2652_; lean_object* v_v_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2675_; 
v_k_2652_ = lean_ctor_get(v_r_2398_, 1);
v_v_2653_ = lean_ctor_get(v_r_2398_, 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_r_2398_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; lean_object* v_unused_2677_; lean_object* v_unused_2678_; 
v_unused_2676_ = lean_ctor_get(v_r_2398_, 4);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_r_2398_, 3);
lean_dec(v_unused_2677_);
v_unused_2678_ = lean_ctor_get(v_r_2398_, 0);
lean_dec(v_unused_2678_);
v___x_2655_ = v_r_2398_;
v_isShared_2656_ = v_isSharedCheck_2675_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_v_2653_);
lean_inc(v_k_2652_);
lean_dec(v_r_2398_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2675_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_k_2657_; lean_object* v_v_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2671_; 
v_k_2657_ = lean_ctor_get(v_l_2633_, 1);
v_v_2658_ = lean_ctor_get(v_l_2633_, 2);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_l_2633_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; lean_object* v_unused_2673_; lean_object* v_unused_2674_; 
v_unused_2672_ = lean_ctor_get(v_l_2633_, 4);
lean_dec(v_unused_2672_);
v_unused_2673_ = lean_ctor_get(v_l_2633_, 3);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_l_2633_, 0);
lean_dec(v_unused_2674_);
v___x_2660_ = v_l_2633_;
v_isShared_2661_ = v_isSharedCheck_2671_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_v_2658_);
lean_inc(v_k_2657_);
lean_dec(v_l_2633_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2671_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2662_ = lean_unsigned_to_nat(3u);
v___x_2663_ = lean_unsigned_to_nat(1u);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 4, v_r_2634_);
lean_ctor_set(v___x_2660_, 3, v_r_2634_);
lean_ctor_set(v___x_2660_, 2, v_v_2396_);
lean_ctor_set(v___x_2660_, 1, v_k_2395_);
lean_ctor_set(v___x_2660_, 0, v___x_2663_);
v___x_2665_ = v___x_2660_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_r_2634_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_r_2634_);
v___x_2665_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 3, v_r_2634_);
lean_ctor_set(v___x_2655_, 0, v___x_2663_);
v___x_2667_ = v___x_2655_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_k_2652_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_v_2653_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v_r_2634_);
lean_ctor_set(v_reuseFailAlloc_2669_, 4, v_r_2634_);
v___x_2667_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2662_);
lean_ctor_set(v___x_2668_, 1, v_k_2657_);
lean_ctor_set(v___x_2668_, 2, v_v_2658_);
lean_ctor_set(v___x_2668_, 3, v___x_2665_);
lean_ctor_set(v___x_2668_, 4, v___x_2667_);
return v___x_2668_;
}
}
}
}
}
}
else
{
lean_object* v_r_2679_; 
v_r_2679_ = lean_ctor_get(v_r_2398_, 4);
lean_inc(v_r_2679_);
if (lean_obj_tag(v_r_2679_) == 0)
{
lean_object* v_k_2680_; lean_object* v_v_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2691_; 
v_k_2680_ = lean_ctor_get(v_r_2398_, 1);
v_v_2681_ = lean_ctor_get(v_r_2398_, 2);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_r_2398_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; lean_object* v_unused_2693_; lean_object* v_unused_2694_; 
v_unused_2692_ = lean_ctor_get(v_r_2398_, 4);
lean_dec(v_unused_2692_);
v_unused_2693_ = lean_ctor_get(v_r_2398_, 3);
lean_dec(v_unused_2693_);
v_unused_2694_ = lean_ctor_get(v_r_2398_, 0);
lean_dec(v_unused_2694_);
v___x_2683_ = v_r_2398_;
v_isShared_2684_ = v_isSharedCheck_2691_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_v_2681_);
lean_inc(v_k_2680_);
lean_dec(v_r_2398_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2691_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_unsigned_to_nat(3u);
v___x_2686_ = lean_unsigned_to_nat(1u);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 4, v_l_2633_);
lean_ctor_set(v___x_2683_, 2, v_v_2396_);
lean_ctor_set(v___x_2683_, 1, v_k_2395_);
lean_ctor_set(v___x_2683_, 0, v___x_2686_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_l_2633_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_l_2633_);
v___x_2688_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2685_);
lean_ctor_set(v___x_2689_, 1, v_k_2680_);
lean_ctor_set(v___x_2689_, 2, v_v_2681_);
lean_ctor_set(v___x_2689_, 3, v___x_2688_);
lean_ctor_set(v___x_2689_, 4, v_r_2679_);
return v___x_2689_;
}
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_unsigned_to_nat(2u);
v___x_2696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v_k_2395_);
lean_ctor_set(v___x_2696_, 2, v_v_2396_);
lean_ctor_set(v___x_2696_, 3, v_r_2679_);
lean_ctor_set(v___x_2696_, 4, v_r_2398_);
return v___x_2696_;
}
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_k_2395_);
lean_ctor_set(v___x_2698_, 2, v_v_2396_);
lean_ctor_set(v___x_2698_, 3, v_r_2398_);
lean_ctor_set(v___x_2698_, 4, v_r_2398_);
return v___x_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance(lean_object* v_00_u03b1_2699_, lean_object* v_00_u03b2_2700_, lean_object* v_k_2701_, lean_object* v_v_2702_, lean_object* v_l_2703_, lean_object* v_r_2704_, lean_object* v_hl_2705_, lean_object* v_hr_2706_, lean_object* v_h_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2701_, v_v_2702_, v_l_2703_, v_r_2704_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(lean_object* v_msg_2709_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_box(1);
v___x_2711_ = lean_panic_fn(v___x_2710_, v_msg_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0(lean_object* v_00_u03b1_2712_, lean_object* v_00_u03b2_2713_, lean_object* v_msg_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v_msg_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2718_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2719_ = lean_unsigned_to_nat(36u);
v___x_2720_ = lean_unsigned_to_nat(393u);
v___x_2721_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2722_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2723_ = l_mkPanicMessageWithDecl(v___x_2722_, v___x_2721_, v___x_2720_, v___x_2719_, v___x_2718_);
return v___x_2723_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2724_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2725_ = lean_unsigned_to_nat(22u);
v___x_2726_ = lean_unsigned_to_nat(394u);
v___x_2727_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2728_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2729_ = l_mkPanicMessageWithDecl(v___x_2728_, v___x_2727_, v___x_2726_, v___x_2725_, v___x_2724_);
return v___x_2729_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2730_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2731_ = lean_unsigned_to_nat(36u);
v___x_2732_ = lean_unsigned_to_nat(383u);
v___x_2733_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2734_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2735_ = l_mkPanicMessageWithDecl(v___x_2734_, v___x_2733_, v___x_2732_, v___x_2731_, v___x_2730_);
return v___x_2735_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2736_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2737_ = lean_unsigned_to_nat(22u);
v___x_2738_ = lean_unsigned_to_nat(384u);
v___x_2739_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2740_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2741_ = l_mkPanicMessageWithDecl(v___x_2740_, v___x_2739_, v___x_2738_, v___x_2737_, v___x_2736_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(lean_object* v_k_2742_, lean_object* v_v_2743_, lean_object* v_l_2744_, lean_object* v_r_2745_){
_start:
{
if (lean_obj_tag(v_l_2744_) == 0)
{
if (lean_obj_tag(v_r_2745_) == 0)
{
lean_object* v_size_2746_; lean_object* v_k_2747_; lean_object* v_v_2748_; lean_object* v_l_2749_; lean_object* v_r_2750_; lean_object* v_size_2751_; lean_object* v_k_2752_; lean_object* v_v_2753_; lean_object* v_l_2754_; lean_object* v_r_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_size_2746_ = lean_ctor_get(v_l_2744_, 0);
v_k_2747_ = lean_ctor_get(v_l_2744_, 1);
v_v_2748_ = lean_ctor_get(v_l_2744_, 2);
v_l_2749_ = lean_ctor_get(v_l_2744_, 3);
v_r_2750_ = lean_ctor_get(v_l_2744_, 4);
lean_inc(v_r_2750_);
v_size_2751_ = lean_ctor_get(v_r_2745_, 0);
v_k_2752_ = lean_ctor_get(v_r_2745_, 1);
v_v_2753_ = lean_ctor_get(v_r_2745_, 2);
v_l_2754_ = lean_ctor_get(v_r_2745_, 3);
lean_inc(v_l_2754_);
v_r_2755_ = lean_ctor_get(v_r_2745_, 4);
v___x_2756_ = lean_unsigned_to_nat(3u);
v___x_2757_ = lean_nat_mul(v___x_2756_, v_size_2746_);
v___x_2758_ = lean_nat_dec_lt(v___x_2757_, v_size_2751_);
lean_dec(v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
lean_dec(v_l_2754_);
v___x_2759_ = lean_nat_mul(v___x_2756_, v_size_2751_);
v___x_2760_ = lean_nat_dec_lt(v___x_2759_, v_size_2746_);
lean_dec(v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v_r_2750_);
v___x_2761_ = lean_unsigned_to_nat(1u);
v___x_2762_ = lean_nat_add(v___x_2761_, v_size_2746_);
v___x_2763_ = lean_nat_add(v___x_2762_, v_size_2751_);
lean_dec(v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
lean_ctor_set(v___x_2764_, 1, v_k_2742_);
lean_ctor_set(v___x_2764_, 2, v_v_2743_);
lean_ctor_set(v___x_2764_, 3, v_l_2744_);
lean_ctor_set(v___x_2764_, 4, v_r_2745_);
return v___x_2764_;
}
else
{
lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2834_; 
lean_inc(v_l_2749_);
lean_inc(v_v_2748_);
lean_inc(v_k_2747_);
lean_inc(v_size_2746_);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_l_2744_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; lean_object* v_unused_2836_; lean_object* v_unused_2837_; lean_object* v_unused_2838_; lean_object* v_unused_2839_; 
v_unused_2835_ = lean_ctor_get(v_l_2744_, 4);
lean_dec(v_unused_2835_);
v_unused_2836_ = lean_ctor_get(v_l_2744_, 3);
lean_dec(v_unused_2836_);
v_unused_2837_ = lean_ctor_get(v_l_2744_, 2);
lean_dec(v_unused_2837_);
v_unused_2838_ = lean_ctor_get(v_l_2744_, 1);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_l_2744_, 0);
lean_dec(v_unused_2839_);
v___x_2766_ = v_l_2744_;
v_isShared_2767_ = v_isSharedCheck_2834_;
goto v_resetjp_2765_;
}
else
{
lean_dec(v_l_2744_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2834_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
if (lean_obj_tag(v_l_2749_) == 0)
{
if (lean_obj_tag(v_r_2750_) == 0)
{
lean_object* v_size_2768_; lean_object* v_size_2769_; lean_object* v_k_2770_; lean_object* v_v_2771_; lean_object* v_l_2772_; lean_object* v_r_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v_size_2768_ = lean_ctor_get(v_l_2749_, 0);
v_size_2769_ = lean_ctor_get(v_r_2750_, 0);
v_k_2770_ = lean_ctor_get(v_r_2750_, 1);
v_v_2771_ = lean_ctor_get(v_r_2750_, 2);
v_l_2772_ = lean_ctor_get(v_r_2750_, 3);
v_r_2773_ = lean_ctor_get(v_r_2750_, 4);
v___x_2774_ = lean_unsigned_to_nat(2u);
v___x_2775_ = lean_nat_mul(v___x_2774_, v_size_2768_);
v___x_2776_ = lean_nat_dec_lt(v_size_2769_, v___x_2775_);
lean_dec(v___x_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2815_; 
lean_inc(v_r_2773_);
lean_inc(v_l_2772_);
lean_inc(v_v_2771_);
lean_inc(v_k_2770_);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_r_2750_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; lean_object* v_unused_2817_; lean_object* v_unused_2818_; lean_object* v_unused_2819_; lean_object* v_unused_2820_; 
v_unused_2816_ = lean_ctor_get(v_r_2750_, 4);
lean_dec(v_unused_2816_);
v_unused_2817_ = lean_ctor_get(v_r_2750_, 3);
lean_dec(v_unused_2817_);
v_unused_2818_ = lean_ctor_get(v_r_2750_, 2);
lean_dec(v_unused_2818_);
v_unused_2819_ = lean_ctor_get(v_r_2750_, 1);
lean_dec(v_unused_2819_);
v_unused_2820_ = lean_ctor_get(v_r_2750_, 0);
lean_dec(v_unused_2820_);
v___x_2778_ = v_r_2750_;
v_isShared_2779_ = v_isSharedCheck_2815_;
goto v_resetjp_2777_;
}
else
{
lean_dec(v_r_2750_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2815_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___x_2803_; lean_object* v___y_2805_; 
v___x_2780_ = lean_unsigned_to_nat(1u);
v___x_2781_ = lean_nat_add(v___x_2780_, v_size_2746_);
lean_dec(v_size_2746_);
v___x_2782_ = lean_nat_add(v___x_2781_, v_size_2751_);
lean_dec(v___x_2781_);
v___x_2803_ = lean_nat_add(v___x_2780_, v_size_2768_);
if (lean_obj_tag(v_l_2772_) == 0)
{
lean_object* v_size_2813_; 
v_size_2813_ = lean_ctor_get(v_l_2772_, 0);
lean_inc(v_size_2813_);
v___y_2805_ = v_size_2813_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_unsigned_to_nat(0u);
v___y_2805_ = v___x_2814_;
goto v___jp_2804_;
}
v___jp_2783_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = lean_nat_add(v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec(v___y_2785_);
lean_inc_ref(v_r_2745_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 4, v_r_2745_);
lean_ctor_set(v___x_2778_, 3, v_r_2773_);
lean_ctor_set(v___x_2778_, 2, v_v_2743_);
lean_ctor_set(v___x_2778_, 1, v_k_2742_);
lean_ctor_set(v___x_2778_, 0, v___x_2787_);
v___x_2789_ = v___x_2778_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2802_, 3, v_r_2773_);
lean_ctor_set(v_reuseFailAlloc_2802_, 4, v_r_2745_);
v___x_2789_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_isSharedCheck_2796_ = !lean_is_exclusive(v_r_2745_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; lean_object* v_unused_2800_; lean_object* v_unused_2801_; 
v_unused_2797_ = lean_ctor_get(v_r_2745_, 4);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_r_2745_, 3);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_r_2745_, 2);
lean_dec(v_unused_2799_);
v_unused_2800_ = lean_ctor_get(v_r_2745_, 1);
lean_dec(v_unused_2800_);
v_unused_2801_ = lean_ctor_get(v_r_2745_, 0);
lean_dec(v_unused_2801_);
v___x_2791_ = v_r_2745_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v_r_2745_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 4, v___x_2789_);
lean_ctor_set(v___x_2791_, 3, v___y_2784_);
lean_ctor_set(v___x_2791_, 2, v_v_2771_);
lean_ctor_set(v___x_2791_, 1, v_k_2770_);
lean_ctor_set(v___x_2791_, 0, v___x_2782_);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_k_2770_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_v_2771_);
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v___y_2784_);
lean_ctor_set(v_reuseFailAlloc_2795_, 4, v___x_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
v___jp_2804_:
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2806_ = lean_nat_add(v___x_2803_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec(v___x_2803_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v_l_2772_);
lean_ctor_set(v___x_2766_, 0, v___x_2806_);
v___x_2808_ = v___x_2766_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2747_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2748_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_l_2749_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_l_2772_);
v___x_2808_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_nat_add(v___x_2780_, v_size_2751_);
if (lean_obj_tag(v_r_2773_) == 0)
{
lean_object* v_size_2810_; 
v_size_2810_ = lean_ctor_get(v_r_2773_, 0);
lean_inc(v_size_2810_);
v___y_2784_ = v___x_2808_;
v___y_2785_ = v___x_2809_;
v___y_2786_ = v_size_2810_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_unsigned_to_nat(0u);
v___y_2784_ = v___x_2808_;
v___y_2785_ = v___x_2809_;
v___y_2786_ = v___x_2811_;
goto v___jp_2783_;
}
}
}
}
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2821_ = lean_unsigned_to_nat(1u);
v___x_2822_ = lean_nat_add(v___x_2821_, v_size_2746_);
lean_dec(v_size_2746_);
v___x_2823_ = lean_nat_add(v___x_2822_, v_size_2751_);
lean_dec(v___x_2822_);
v___x_2824_ = lean_nat_add(v___x_2821_, v_size_2751_);
v___x_2825_ = lean_nat_add(v___x_2824_, v_size_2769_);
lean_dec(v___x_2824_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v_r_2745_);
lean_ctor_set(v___x_2766_, 3, v_r_2750_);
lean_ctor_set(v___x_2766_, 2, v_v_2743_);
lean_ctor_set(v___x_2766_, 1, v_k_2742_);
lean_ctor_set(v___x_2766_, 0, v___x_2825_);
v___x_2827_ = v___x_2766_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_r_2750_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_r_2745_);
v___x_2827_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2823_);
lean_ctor_set(v___x_2828_, 1, v_k_2747_);
lean_ctor_set(v___x_2828_, 2, v_v_2748_);
lean_ctor_set(v___x_2828_, 3, v_l_2749_);
lean_ctor_set(v___x_2828_, 4, v___x_2827_);
return v___x_2828_;
}
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v_l_2749_);
lean_del_object(v___x_2766_);
lean_dec(v_v_2748_);
lean_dec(v_k_2747_);
lean_dec(v_size_2746_);
lean_dec_ref(v_r_2745_);
lean_dec(v_v_2743_);
lean_dec(v_k_2742_);
v___x_2830_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2);
v___x_2831_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2830_);
return v___x_2831_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2766_);
lean_dec(v_r_2750_);
lean_dec(v_v_2748_);
lean_dec(v_k_2747_);
lean_dec_ref(v_r_2745_);
lean_dec(v_size_2746_);
lean_dec(v_v_2743_);
lean_dec(v_k_2742_);
v___x_2832_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3);
v___x_2833_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2832_);
return v___x_2833_;
}
}
}
}
else
{
lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2907_; 
lean_inc(v_r_2755_);
lean_inc(v_v_2753_);
lean_inc(v_k_2752_);
lean_inc(v_size_2751_);
lean_dec(v_r_2750_);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_r_2745_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; lean_object* v_unused_2909_; lean_object* v_unused_2910_; lean_object* v_unused_2911_; lean_object* v_unused_2912_; 
v_unused_2908_ = lean_ctor_get(v_r_2745_, 4);
lean_dec(v_unused_2908_);
v_unused_2909_ = lean_ctor_get(v_r_2745_, 3);
lean_dec(v_unused_2909_);
v_unused_2910_ = lean_ctor_get(v_r_2745_, 2);
lean_dec(v_unused_2910_);
v_unused_2911_ = lean_ctor_get(v_r_2745_, 1);
lean_dec(v_unused_2911_);
v_unused_2912_ = lean_ctor_get(v_r_2745_, 0);
lean_dec(v_unused_2912_);
v___x_2841_ = v_r_2745_;
v_isShared_2842_ = v_isSharedCheck_2907_;
goto v_resetjp_2840_;
}
else
{
lean_dec(v_r_2745_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2907_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
if (lean_obj_tag(v_l_2754_) == 0)
{
if (lean_obj_tag(v_r_2755_) == 0)
{
lean_object* v_size_2843_; lean_object* v_k_2844_; lean_object* v_v_2845_; lean_object* v_l_2846_; lean_object* v_r_2847_; lean_object* v_size_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_size_2843_ = lean_ctor_get(v_l_2754_, 0);
v_k_2844_ = lean_ctor_get(v_l_2754_, 1);
v_v_2845_ = lean_ctor_get(v_l_2754_, 2);
v_l_2846_ = lean_ctor_get(v_l_2754_, 3);
v_r_2847_ = lean_ctor_get(v_l_2754_, 4);
v_size_2848_ = lean_ctor_get(v_r_2755_, 0);
v___x_2849_ = lean_unsigned_to_nat(2u);
v___x_2850_ = lean_nat_mul(v___x_2849_, v_size_2848_);
v___x_2851_ = lean_nat_dec_lt(v_size_2843_, v___x_2850_);
lean_dec(v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2878_; 
lean_inc(v_r_2847_);
lean_inc(v_l_2846_);
lean_inc(v_v_2845_);
lean_inc(v_k_2844_);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_l_2754_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; lean_object* v_unused_2880_; lean_object* v_unused_2881_; lean_object* v_unused_2882_; lean_object* v_unused_2883_; 
v_unused_2879_ = lean_ctor_get(v_l_2754_, 4);
lean_dec(v_unused_2879_);
v_unused_2880_ = lean_ctor_get(v_l_2754_, 3);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_l_2754_, 2);
lean_dec(v_unused_2881_);
v_unused_2882_ = lean_ctor_get(v_l_2754_, 1);
lean_dec(v_unused_2882_);
v_unused_2883_ = lean_ctor_get(v_l_2754_, 0);
lean_dec(v_unused_2883_);
v___x_2853_ = v_l_2754_;
v_isShared_2854_ = v_isSharedCheck_2878_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v_l_2754_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2878_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2870_; 
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_2856_ = lean_nat_add(v___x_2855_, v_size_2746_);
v___x_2857_ = lean_nat_add(v___x_2856_, v_size_2751_);
lean_dec(v_size_2751_);
if (lean_obj_tag(v_l_2846_) == 0)
{
lean_object* v_size_2876_; 
v_size_2876_ = lean_ctor_get(v_l_2846_, 0);
lean_inc(v_size_2876_);
v___y_2870_ = v_size_2876_;
goto v___jp_2869_;
}
else
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_unsigned_to_nat(0u);
v___y_2870_ = v___x_2877_;
goto v___jp_2869_;
}
v___jp_2858_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = lean_nat_add(v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 4, v_r_2755_);
lean_ctor_set(v___x_2853_, 3, v_r_2847_);
lean_ctor_set(v___x_2853_, 2, v_v_2753_);
lean_ctor_set(v___x_2853_, 1, v_k_2752_);
lean_ctor_set(v___x_2853_, 0, v___x_2862_);
v___x_2864_ = v___x_2853_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_k_2752_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_v_2753_);
lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_r_2847_);
lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_r_2755_);
v___x_2864_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2866_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 4, v___x_2864_);
lean_ctor_set(v___x_2841_, 3, v___y_2859_);
lean_ctor_set(v___x_2841_, 2, v_v_2845_);
lean_ctor_set(v___x_2841_, 1, v_k_2844_);
lean_ctor_set(v___x_2841_, 0, v___x_2857_);
v___x_2866_ = v___x_2841_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_k_2844_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_v_2845_);
lean_ctor_set(v_reuseFailAlloc_2867_, 3, v___y_2859_);
lean_ctor_set(v_reuseFailAlloc_2867_, 4, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
v___jp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_nat_add(v___x_2856_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec(v___x_2856_);
v___x_2872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v_k_2742_);
lean_ctor_set(v___x_2872_, 2, v_v_2743_);
lean_ctor_set(v___x_2872_, 3, v_l_2744_);
lean_ctor_set(v___x_2872_, 4, v_l_2846_);
v___x_2873_ = lean_nat_add(v___x_2855_, v_size_2848_);
if (lean_obj_tag(v_r_2847_) == 0)
{
lean_object* v_size_2874_; 
v_size_2874_ = lean_ctor_get(v_r_2847_, 0);
lean_inc(v_size_2874_);
v___y_2859_ = v___x_2872_;
v___y_2860_ = v___x_2873_;
v___y_2861_ = v_size_2874_;
goto v___jp_2858_;
}
else
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_unsigned_to_nat(0u);
v___y_2859_ = v___x_2872_;
v___y_2860_ = v___x_2873_;
v___y_2861_ = v___x_2875_;
goto v___jp_2858_;
}
}
}
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_add(v___x_2884_, v_size_2746_);
v___x_2886_ = lean_nat_add(v___x_2885_, v_size_2751_);
lean_dec(v_size_2751_);
v___x_2887_ = lean_nat_add(v___x_2885_, v_size_2843_);
lean_dec(v___x_2885_);
lean_inc_ref(v_l_2744_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 4, v_l_2754_);
lean_ctor_set(v___x_2841_, 3, v_l_2744_);
lean_ctor_set(v___x_2841_, 2, v_v_2743_);
lean_ctor_set(v___x_2841_, 1, v_k_2742_);
lean_ctor_set(v___x_2841_, 0, v___x_2887_);
v___x_2889_ = v___x_2841_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_l_2744_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_l_2754_);
v___x_2889_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_isSharedCheck_2896_ = !lean_is_exclusive(v_l_2744_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; lean_object* v_unused_2898_; lean_object* v_unused_2899_; lean_object* v_unused_2900_; lean_object* v_unused_2901_; 
v_unused_2897_ = lean_ctor_get(v_l_2744_, 4);
lean_dec(v_unused_2897_);
v_unused_2898_ = lean_ctor_get(v_l_2744_, 3);
lean_dec(v_unused_2898_);
v_unused_2899_ = lean_ctor_get(v_l_2744_, 2);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_l_2744_, 1);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_l_2744_, 0);
lean_dec(v_unused_2901_);
v___x_2891_ = v_l_2744_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v_l_2744_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 4, v_r_2755_);
lean_ctor_set(v___x_2891_, 3, v___x_2889_);
lean_ctor_set(v___x_2891_, 2, v_v_2753_);
lean_ctor_set(v___x_2891_, 1, v_k_2752_);
lean_ctor_set(v___x_2891_, 0, v___x_2886_);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_k_2752_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_v_2753_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_r_2755_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec_ref(v_l_2754_);
lean_del_object(v___x_2841_);
lean_dec(v_v_2753_);
lean_dec(v_k_2752_);
lean_dec(v_size_2751_);
lean_dec_ref(v_l_2744_);
lean_dec(v_v_2743_);
lean_dec(v_k_2742_);
v___x_2903_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4);
v___x_2904_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2903_);
return v___x_2904_;
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_del_object(v___x_2841_);
lean_dec(v_r_2755_);
lean_dec(v_v_2753_);
lean_dec(v_k_2752_);
lean_dec(v_size_2751_);
lean_dec_ref(v_l_2744_);
lean_dec(v_v_2743_);
lean_dec(v_k_2742_);
v___x_2905_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5);
v___x_2906_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2905_);
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_l_2913_; 
v_l_2913_ = lean_ctor_get(v_l_2744_, 3);
if (lean_obj_tag(v_l_2913_) == 0)
{
lean_object* v_r_2914_; 
lean_inc_ref(v_l_2913_);
v_r_2914_ = lean_ctor_get(v_l_2744_, 4);
lean_inc(v_r_2914_);
if (lean_obj_tag(v_r_2914_) == 0)
{
lean_object* v_size_2915_; lean_object* v_k_2916_; lean_object* v_v_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2940_; 
v_size_2915_ = lean_ctor_get(v_l_2744_, 0);
v_k_2916_ = lean_ctor_get(v_l_2744_, 1);
v_v_2917_ = lean_ctor_get(v_l_2744_, 2);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_l_2744_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; lean_object* v_unused_2942_; 
v_unused_2941_ = lean_ctor_get(v_l_2744_, 4);
lean_dec(v_unused_2941_);
v_unused_2942_ = lean_ctor_get(v_l_2744_, 3);
lean_dec(v_unused_2942_);
v___x_2919_ = v_l_2744_;
v_isShared_2920_ = v_isSharedCheck_2940_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_v_2917_);
lean_inc(v_k_2916_);
lean_inc(v_size_2915_);
lean_dec(v_l_2744_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2940_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_size_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v_size_2921_ = lean_ctor_get(v_r_2914_, 0);
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_add(v___x_2922_, v_size_2915_);
lean_dec(v_size_2915_);
v___x_2924_ = lean_nat_add(v___x_2922_, v_size_2921_);
lean_inc_ref(v_r_2914_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 4, v_r_2745_);
lean_ctor_set(v___x_2919_, 3, v_r_2914_);
lean_ctor_set(v___x_2919_, 2, v_v_2743_);
lean_ctor_set(v___x_2919_, 1, v_k_2742_);
lean_ctor_set(v___x_2919_, 0, v___x_2924_);
v___x_2926_ = v___x_2919_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_r_2914_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_r_2745_);
v___x_2926_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
v_isSharedCheck_2933_ = !lean_is_exclusive(v_r_2914_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; lean_object* v_unused_2935_; lean_object* v_unused_2936_; lean_object* v_unused_2937_; lean_object* v_unused_2938_; 
v_unused_2934_ = lean_ctor_get(v_r_2914_, 4);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_r_2914_, 3);
lean_dec(v_unused_2935_);
v_unused_2936_ = lean_ctor_get(v_r_2914_, 2);
lean_dec(v_unused_2936_);
v_unused_2937_ = lean_ctor_get(v_r_2914_, 1);
lean_dec(v_unused_2937_);
v_unused_2938_ = lean_ctor_get(v_r_2914_, 0);
lean_dec(v_unused_2938_);
v___x_2928_ = v_r_2914_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_dec(v_r_2914_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 4, v___x_2926_);
lean_ctor_set(v___x_2928_, 3, v_l_2913_);
lean_ctor_set(v___x_2928_, 2, v_v_2917_);
lean_ctor_set(v___x_2928_, 1, v_k_2916_);
lean_ctor_set(v___x_2928_, 0, v___x_2923_);
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_k_2916_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_v_2917_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_l_2913_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v___x_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
else
{
lean_object* v_k_2943_; lean_object* v_v_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2954_; 
v_k_2943_ = lean_ctor_get(v_l_2744_, 1);
v_v_2944_ = lean_ctor_get(v_l_2744_, 2);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_l_2744_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; lean_object* v_unused_2956_; lean_object* v_unused_2957_; 
v_unused_2955_ = lean_ctor_get(v_l_2744_, 4);
lean_dec(v_unused_2955_);
v_unused_2956_ = lean_ctor_get(v_l_2744_, 3);
lean_dec(v_unused_2956_);
v_unused_2957_ = lean_ctor_get(v_l_2744_, 0);
lean_dec(v_unused_2957_);
v___x_2946_ = v_l_2744_;
v_isShared_2947_ = v_isSharedCheck_2954_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_v_2944_);
lean_inc(v_k_2943_);
lean_dec(v_l_2744_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2954_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2948_ = lean_unsigned_to_nat(3u);
v___x_2949_ = lean_unsigned_to_nat(1u);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 3, v_r_2914_);
lean_ctor_set(v___x_2946_, 2, v_v_2743_);
lean_ctor_set(v___x_2946_, 1, v_k_2742_);
lean_ctor_set(v___x_2946_, 0, v___x_2949_);
v___x_2951_ = v___x_2946_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_r_2914_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_r_2914_);
v___x_2951_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2948_);
lean_ctor_set(v___x_2952_, 1, v_k_2943_);
lean_ctor_set(v___x_2952_, 2, v_v_2944_);
lean_ctor_set(v___x_2952_, 3, v_l_2913_);
lean_ctor_set(v___x_2952_, 4, v___x_2951_);
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_r_2958_; 
v_r_2958_ = lean_ctor_get(v_l_2744_, 4);
lean_inc(v_r_2958_);
if (lean_obj_tag(v_r_2958_) == 0)
{
lean_object* v_k_2959_; lean_object* v_v_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2982_; 
lean_inc(v_l_2913_);
v_k_2959_ = lean_ctor_get(v_l_2744_, 1);
v_v_2960_ = lean_ctor_get(v_l_2744_, 2);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_l_2744_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; lean_object* v_unused_2984_; lean_object* v_unused_2985_; 
v_unused_2983_ = lean_ctor_get(v_l_2744_, 4);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_l_2744_, 3);
lean_dec(v_unused_2984_);
v_unused_2985_ = lean_ctor_get(v_l_2744_, 0);
lean_dec(v_unused_2985_);
v___x_2962_ = v_l_2744_;
v_isShared_2963_ = v_isSharedCheck_2982_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_v_2960_);
lean_inc(v_k_2959_);
lean_dec(v_l_2744_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2982_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_k_2964_; lean_object* v_v_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2978_; 
v_k_2964_ = lean_ctor_get(v_r_2958_, 1);
v_v_2965_ = lean_ctor_get(v_r_2958_, 2);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_r_2958_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; lean_object* v_unused_2980_; lean_object* v_unused_2981_; 
v_unused_2979_ = lean_ctor_get(v_r_2958_, 4);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_r_2958_, 3);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_r_2958_, 0);
lean_dec(v_unused_2981_);
v___x_2967_ = v_r_2958_;
v_isShared_2968_ = v_isSharedCheck_2978_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_v_2965_);
lean_inc(v_k_2964_);
lean_dec(v_r_2958_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2978_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = lean_unsigned_to_nat(3u);
v___x_2970_ = lean_unsigned_to_nat(1u);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 4, v_l_2913_);
lean_ctor_set(v___x_2967_, 3, v_l_2913_);
lean_ctor_set(v___x_2967_, 2, v_v_2960_);
lean_ctor_set(v___x_2967_, 1, v_k_2959_);
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_k_2959_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_v_2960_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_l_2913_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v_l_2913_);
v___x_2972_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 4, v_l_2913_);
lean_ctor_set(v___x_2962_, 2, v_v_2743_);
lean_ctor_set(v___x_2962_, 1, v_k_2742_);
lean_ctor_set(v___x_2962_, 0, v___x_2970_);
v___x_2974_ = v___x_2962_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_l_2913_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_l_2913_);
v___x_2974_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2969_);
lean_ctor_set(v___x_2975_, 1, v_k_2964_);
lean_ctor_set(v___x_2975_, 2, v_v_2965_);
lean_ctor_set(v___x_2975_, 3, v___x_2972_);
lean_ctor_set(v___x_2975_, 4, v___x_2974_);
return v___x_2975_;
}
}
}
}
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_unsigned_to_nat(2u);
v___x_2987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v_k_2742_);
lean_ctor_set(v___x_2987_, 2, v_v_2743_);
lean_ctor_set(v___x_2987_, 3, v_l_2744_);
lean_ctor_set(v___x_2987_, 4, v_r_2958_);
return v___x_2987_;
}
}
}
}
else
{
if (lean_obj_tag(v_r_2745_) == 0)
{
lean_object* v_l_2988_; 
v_l_2988_ = lean_ctor_get(v_r_2745_, 3);
lean_inc(v_l_2988_);
if (lean_obj_tag(v_l_2988_) == 0)
{
lean_object* v_r_2989_; 
v_r_2989_ = lean_ctor_get(v_r_2745_, 4);
lean_inc(v_r_2989_);
if (lean_obj_tag(v_r_2989_) == 0)
{
lean_object* v_size_2990_; lean_object* v_k_2991_; lean_object* v_v_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3004_; 
v_size_2990_ = lean_ctor_get(v_r_2745_, 0);
v_k_2991_ = lean_ctor_get(v_r_2745_, 1);
v_v_2992_ = lean_ctor_get(v_r_2745_, 2);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_r_2745_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; lean_object* v_unused_3006_; 
v_unused_3005_ = lean_ctor_get(v_r_2745_, 4);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_r_2745_, 3);
lean_dec(v_unused_3006_);
v___x_2994_ = v_r_2745_;
v_isShared_2995_ = v_isSharedCheck_3004_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_v_2992_);
lean_inc(v_k_2991_);
lean_inc(v_size_2990_);
lean_dec(v_r_2745_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3004_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v_size_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v_size_2996_ = lean_ctor_get(v_l_2988_, 0);
v___x_2997_ = lean_unsigned_to_nat(1u);
v___x_2998_ = lean_nat_add(v___x_2997_, v_size_2990_);
lean_dec(v_size_2990_);
v___x_2999_ = lean_nat_add(v___x_2997_, v_size_2996_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 4, v_l_2988_);
lean_ctor_set(v___x_2994_, 3, v_l_2744_);
lean_ctor_set(v___x_2994_, 2, v_v_2743_);
lean_ctor_set(v___x_2994_, 1, v_k_2742_);
lean_ctor_set(v___x_2994_, 0, v___x_2999_);
v___x_3001_ = v___x_2994_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v_l_2744_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v_l_2988_);
v___x_3001_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3002_, 0, v___x_2998_);
lean_ctor_set(v___x_3002_, 1, v_k_2991_);
lean_ctor_set(v___x_3002_, 2, v_v_2992_);
lean_ctor_set(v___x_3002_, 3, v___x_3001_);
lean_ctor_set(v___x_3002_, 4, v_r_2989_);
return v___x_3002_;
}
}
}
else
{
lean_object* v_k_3007_; lean_object* v_v_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3030_; 
v_k_3007_ = lean_ctor_get(v_r_2745_, 1);
v_v_3008_ = lean_ctor_get(v_r_2745_, 2);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_r_2745_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; lean_object* v_unused_3032_; lean_object* v_unused_3033_; 
v_unused_3031_ = lean_ctor_get(v_r_2745_, 4);
lean_dec(v_unused_3031_);
v_unused_3032_ = lean_ctor_get(v_r_2745_, 3);
lean_dec(v_unused_3032_);
v_unused_3033_ = lean_ctor_get(v_r_2745_, 0);
lean_dec(v_unused_3033_);
v___x_3010_ = v_r_2745_;
v_isShared_3011_ = v_isSharedCheck_3030_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_v_3008_);
lean_inc(v_k_3007_);
lean_dec(v_r_2745_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3030_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v_k_3012_; lean_object* v_v_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3026_; 
v_k_3012_ = lean_ctor_get(v_l_2988_, 1);
v_v_3013_ = lean_ctor_get(v_l_2988_, 2);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_l_2988_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; lean_object* v_unused_3028_; lean_object* v_unused_3029_; 
v_unused_3027_ = lean_ctor_get(v_l_2988_, 4);
lean_dec(v_unused_3027_);
v_unused_3028_ = lean_ctor_get(v_l_2988_, 3);
lean_dec(v_unused_3028_);
v_unused_3029_ = lean_ctor_get(v_l_2988_, 0);
lean_dec(v_unused_3029_);
v___x_3015_ = v_l_2988_;
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_v_3013_);
lean_inc(v_k_3012_);
lean_dec(v_l_2988_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3017_ = lean_unsigned_to_nat(3u);
v___x_3018_ = lean_unsigned_to_nat(1u);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 4, v_r_2989_);
lean_ctor_set(v___x_3015_, 3, v_r_2989_);
lean_ctor_set(v___x_3015_, 2, v_v_2743_);
lean_ctor_set(v___x_3015_, 1, v_k_2742_);
lean_ctor_set(v___x_3015_, 0, v___x_3018_);
v___x_3020_ = v___x_3015_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_r_2989_);
lean_ctor_set(v_reuseFailAlloc_3025_, 4, v_r_2989_);
v___x_3020_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3022_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 3, v_r_2989_);
lean_ctor_set(v___x_3010_, 0, v___x_3018_);
v___x_3022_ = v___x_3010_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_k_3007_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_v_3008_);
lean_ctor_set(v_reuseFailAlloc_3024_, 3, v_r_2989_);
lean_ctor_set(v_reuseFailAlloc_3024_, 4, v_r_2989_);
v___x_3022_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3017_);
lean_ctor_set(v___x_3023_, 1, v_k_3012_);
lean_ctor_set(v___x_3023_, 2, v_v_3013_);
lean_ctor_set(v___x_3023_, 3, v___x_3020_);
lean_ctor_set(v___x_3023_, 4, v___x_3022_);
return v___x_3023_;
}
}
}
}
}
}
else
{
lean_object* v_r_3034_; 
v_r_3034_ = lean_ctor_get(v_r_2745_, 4);
lean_inc(v_r_3034_);
if (lean_obj_tag(v_r_3034_) == 0)
{
lean_object* v_k_3035_; lean_object* v_v_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3046_; 
v_k_3035_ = lean_ctor_get(v_r_2745_, 1);
v_v_3036_ = lean_ctor_get(v_r_2745_, 2);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_r_2745_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; lean_object* v_unused_3048_; lean_object* v_unused_3049_; 
v_unused_3047_ = lean_ctor_get(v_r_2745_, 4);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v_r_2745_, 3);
lean_dec(v_unused_3048_);
v_unused_3049_ = lean_ctor_get(v_r_2745_, 0);
lean_dec(v_unused_3049_);
v___x_3038_ = v_r_2745_;
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_v_3036_);
lean_inc(v_k_3035_);
lean_dec(v_r_2745_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3040_ = lean_unsigned_to_nat(3u);
v___x_3041_ = lean_unsigned_to_nat(1u);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 4, v_l_2988_);
lean_ctor_set(v___x_3038_, 2, v_v_2743_);
lean_ctor_set(v___x_3038_, 1, v_k_2742_);
lean_ctor_set(v___x_3038_, 0, v___x_3041_);
v___x_3043_ = v___x_3038_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_3045_, 3, v_l_2988_);
lean_ctor_set(v_reuseFailAlloc_3045_, 4, v_l_2988_);
v___x_3043_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3040_);
lean_ctor_set(v___x_3044_, 1, v_k_3035_);
lean_ctor_set(v___x_3044_, 2, v_v_3036_);
lean_ctor_set(v___x_3044_, 3, v___x_3043_);
lean_ctor_set(v___x_3044_, 4, v_r_3034_);
return v___x_3044_;
}
}
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v_k_2742_);
lean_ctor_set(v___x_3051_, 2, v_v_2743_);
lean_ctor_set(v___x_3051_, 3, v_r_3034_);
lean_ctor_set(v___x_3051_, 4, v_r_2745_);
return v___x_3051_;
}
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_unsigned_to_nat(1u);
v___x_3053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v_k_2742_);
lean_ctor_set(v___x_3053_, 2, v_v_2743_);
lean_ctor_set(v___x_3053_, 3, v_r_2745_);
lean_ctor_set(v___x_3053_, 4, v_r_2745_);
return v___x_3053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21(lean_object* v_00_u03b1_3054_, lean_object* v_00_u03b2_3055_, lean_object* v_k_3056_, lean_object* v_v_3057_, lean_object* v_l_3058_, lean_object* v_r_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(v_k_3056_, v_v_3057_, v_l_3058_, v_r_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin___redArg(lean_object* v_k_3061_, lean_object* v_v_3062_, lean_object* v_l_3063_, lean_object* v_r_3064_){
_start:
{
lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3071_; 
if (lean_obj_tag(v_l_3063_) == 0)
{
lean_object* v_size_3076_; 
v_size_3076_ = lean_ctor_get(v_l_3063_, 0);
lean_inc(v_size_3076_);
v___y_3071_ = v_size_3076_;
goto v___jp_3070_;
}
else
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_unsigned_to_nat(0u);
v___y_3071_ = v___x_3077_;
goto v___jp_3070_;
}
v___jp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_nat_add(v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec(v___y_3066_);
v___x_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v_k_3061_);
lean_ctor_set(v___x_3069_, 2, v_v_3062_);
lean_ctor_set(v___x_3069_, 3, v_l_3063_);
lean_ctor_set(v___x_3069_, 4, v_r_3064_);
return v___x_3069_;
}
v___jp_3070_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = lean_nat_add(v___y_3071_, v___x_3072_);
lean_dec(v___y_3071_);
if (lean_obj_tag(v_r_3064_) == 0)
{
lean_object* v_size_3074_; 
v_size_3074_ = lean_ctor_get(v_r_3064_, 0);
lean_inc(v_size_3074_);
v___y_3066_ = v___x_3073_;
v___y_3067_ = v_size_3074_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_unsigned_to_nat(0u);
v___y_3066_ = v___x_3073_;
v___y_3067_ = v___x_3075_;
goto v___jp_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin(lean_object* v_00_u03b1_3078_, lean_object* v_00_u03b2_3079_, lean_object* v_k_3080_, lean_object* v_v_3081_, lean_object* v_l_3082_, lean_object* v_r_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3080_, v_v_3081_, v_l_3082_, v_r_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL___redArg(lean_object* v_k_3085_, lean_object* v_v_3086_, lean_object* v_l_3087_, lean_object* v_rk_3088_, lean_object* v_rv_3089_, lean_object* v_rl_3090_, lean_object* v_rr_3091_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3085_, v_v_3086_, v_l_3087_, v_rl_3090_);
v___x_3093_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_rk_3088_, v_rv_3089_, v___x_3092_, v_rr_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL(lean_object* v_00_u03b1_3094_, lean_object* v_00_u03b2_3095_, lean_object* v_k_3096_, lean_object* v_v_3097_, lean_object* v_l_3098_, lean_object* v_rk_3099_, lean_object* v_rv_3100_, lean_object* v_rl_3101_, lean_object* v_rr_3102_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Std_DTreeMap_Internal_Impl_singleL___redArg(v_k_3096_, v_v_3097_, v_l_3098_, v_rk_3099_, v_rv_3100_, v_rl_3101_, v_rr_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR___redArg(lean_object* v_k_3104_, lean_object* v_v_3105_, lean_object* v_lk_3106_, lean_object* v_lv_3107_, lean_object* v_ll_3108_, lean_object* v_lr_3109_, lean_object* v_r_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3104_, v_v_3105_, v_lr_3109_, v_r_3110_);
v___x_3112_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_lk_3106_, v_lv_3107_, v_ll_3108_, v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_k_3115_, lean_object* v_v_3116_, lean_object* v_lk_3117_, lean_object* v_lv_3118_, lean_object* v_ll_3119_, lean_object* v_lr_3120_, lean_object* v_r_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Std_DTreeMap_Internal_Impl_singleR___redArg(v_k_3115_, v_v_3116_, v_lk_3117_, v_lv_3118_, v_ll_3119_, v_lr_3120_, v_r_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL___redArg(lean_object* v_k_3123_, lean_object* v_v_3124_, lean_object* v_l_3125_, lean_object* v_rk_3126_, lean_object* v_rv_3127_, lean_object* v_rlk_3128_, lean_object* v_rlv_3129_, lean_object* v_rll_3130_, lean_object* v_rlr_3131_, lean_object* v_rr_3132_){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3123_, v_v_3124_, v_l_3125_, v_rll_3130_);
v___x_3134_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_rk_3126_, v_rv_3127_, v_rlr_3131_, v_rr_3132_);
v___x_3135_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_rlk_3128_, v_rlv_3129_, v___x_3133_, v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL(lean_object* v_00_u03b1_3136_, lean_object* v_00_u03b2_3137_, lean_object* v_k_3138_, lean_object* v_v_3139_, lean_object* v_l_3140_, lean_object* v_rk_3141_, lean_object* v_rv_3142_, lean_object* v_rlk_3143_, lean_object* v_rlv_3144_, lean_object* v_rll_3145_, lean_object* v_rlr_3146_, lean_object* v_rr_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Std_DTreeMap_Internal_Impl_doubleL___redArg(v_k_3138_, v_v_3139_, v_l_3140_, v_rk_3141_, v_rv_3142_, v_rlk_3143_, v_rlv_3144_, v_rll_3145_, v_rlr_3146_, v_rr_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR___redArg(lean_object* v_k_3149_, lean_object* v_v_3150_, lean_object* v_lk_3151_, lean_object* v_lv_3152_, lean_object* v_ll_3153_, lean_object* v_lrk_3154_, lean_object* v_lrv_3155_, lean_object* v_lrl_3156_, lean_object* v_lrr_3157_, lean_object* v_r_3158_){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_lk_3151_, v_lv_3152_, v_ll_3153_, v_lrl_3156_);
v___x_3160_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3149_, v_v_3150_, v_lrr_3157_, v_r_3158_);
v___x_3161_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_lrk_3154_, v_lrv_3155_, v___x_3159_, v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR(lean_object* v_00_u03b1_3162_, lean_object* v_00_u03b2_3163_, lean_object* v_k_3164_, lean_object* v_v_3165_, lean_object* v_lk_3166_, lean_object* v_lv_3167_, lean_object* v_ll_3168_, lean_object* v_lrk_3169_, lean_object* v_lrv_3170_, lean_object* v_lrl_3171_, lean_object* v_lrr_3172_, lean_object* v_r_3173_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Std_DTreeMap_Internal_Impl_doubleR___redArg(v_k_3164_, v_v_3165_, v_lk_3166_, v_lv_3167_, v_ll_3168_, v_lrk_3169_, v_lrv_3170_, v_lrl_3171_, v_lrr_3172_, v_r_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL___redArg(lean_object* v_k_3175_, lean_object* v_v_3176_, lean_object* v_l_3177_, lean_object* v_rk_3178_, lean_object* v_rv_3179_, lean_object* v_rl_3180_, lean_object* v_rr_3181_){
_start:
{
lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3196_; 
if (lean_obj_tag(v_rl_3180_) == 0)
{
lean_object* v_size_3200_; 
v_size_3200_ = lean_ctor_get(v_rl_3180_, 0);
lean_inc(v_size_3200_);
v___y_3196_ = v_size_3200_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_unsigned_to_nat(0u);
v___y_3196_ = v___x_3201_;
goto v___jp_3195_;
}
v___jp_3182_:
{
lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = lean_nat_mul(v___y_3183_, v___y_3185_);
lean_dec(v___y_3185_);
v___x_3187_ = lean_nat_dec_lt(v___y_3184_, v___x_3186_);
lean_dec(v___x_3186_);
lean_dec(v___y_3184_);
if (v___x_3187_ == 0)
{
if (lean_obj_tag(v_rl_3180_) == 0)
{
lean_object* v_k_3188_; lean_object* v_v_3189_; lean_object* v_l_3190_; lean_object* v_r_3191_; lean_object* v___x_3192_; 
v_k_3188_ = lean_ctor_get(v_rl_3180_, 1);
lean_inc(v_k_3188_);
v_v_3189_ = lean_ctor_get(v_rl_3180_, 2);
lean_inc(v_v_3189_);
v_l_3190_ = lean_ctor_get(v_rl_3180_, 3);
lean_inc(v_l_3190_);
v_r_3191_ = lean_ctor_get(v_rl_3180_, 4);
lean_inc(v_r_3191_);
lean_dec_ref(v_rl_3180_);
v___x_3192_ = l_Std_DTreeMap_Internal_Impl_doubleL___redArg(v_k_3175_, v_v_3176_, v_l_3177_, v_rk_3178_, v_rv_3179_, v_k_3188_, v_v_3189_, v_l_3190_, v_r_3191_, v_rr_3181_);
return v___x_3192_;
}
else
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Std_DTreeMap_Internal_Impl_singleL___redArg(v_k_3175_, v_v_3176_, v_l_3177_, v_rk_3178_, v_rv_3179_, v_rl_3180_, v_rr_3181_);
return v___x_3193_;
}
}
else
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Std_DTreeMap_Internal_Impl_singleL___redArg(v_k_3175_, v_v_3176_, v_l_3177_, v_rk_3178_, v_rv_3179_, v_rl_3180_, v_rr_3181_);
return v___x_3194_;
}
}
v___jp_3195_:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_unsigned_to_nat(2u);
if (lean_obj_tag(v_rr_3181_) == 0)
{
lean_object* v_size_3198_; 
v_size_3198_ = lean_ctor_get(v_rr_3181_, 0);
lean_inc(v_size_3198_);
v___y_3183_ = v___x_3197_;
v___y_3184_ = v___y_3196_;
v___y_3185_ = v_size_3198_;
goto v___jp_3182_;
}
else
{
lean_object* v___x_3199_; 
v___x_3199_ = lean_unsigned_to_nat(0u);
v___y_3183_ = v___x_3197_;
v___y_3184_ = v___y_3196_;
v___y_3185_ = v___x_3199_;
goto v___jp_3182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL(lean_object* v_00_u03b1_3202_, lean_object* v_00_u03b2_3203_, lean_object* v_k_3204_, lean_object* v_v_3205_, lean_object* v_l_3206_, lean_object* v_rk_3207_, lean_object* v_rv_3208_, lean_object* v_rl_3209_, lean_object* v_rr_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Std_DTreeMap_Internal_Impl_rotateL___redArg(v_k_3204_, v_v_3205_, v_l_3206_, v_rk_3207_, v_rv_3208_, v_rl_3209_, v_rr_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object* v_l_3212_, lean_object* v_h__1_3213_, lean_object* v_h__2_3214_){
_start:
{
if (lean_obj_tag(v_l_3212_) == 0)
{
lean_object* v_size_3215_; lean_object* v_k_3216_; lean_object* v_v_3217_; lean_object* v_l_3218_; lean_object* v_r_3219_; lean_object* v___x_3220_; 
lean_dec(v_h__1_3213_);
v_size_3215_ = lean_ctor_get(v_l_3212_, 0);
lean_inc(v_size_3215_);
v_k_3216_ = lean_ctor_get(v_l_3212_, 1);
lean_inc(v_k_3216_);
v_v_3217_ = lean_ctor_get(v_l_3212_, 2);
lean_inc(v_v_3217_);
v_l_3218_ = lean_ctor_get(v_l_3212_, 3);
lean_inc(v_l_3218_);
v_r_3219_ = lean_ctor_get(v_l_3212_, 4);
lean_inc(v_r_3219_);
lean_dec_ref(v_l_3212_);
v___x_3220_ = lean_apply_5(v_h__2_3214_, v_size_3215_, v_k_3216_, v_v_3217_, v_l_3218_, v_r_3219_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_dec(v_h__2_3214_);
v___x_3221_ = lean_box(0);
v___x_3222_ = lean_apply_1(v_h__1_3213_, v___x_3221_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object* v_00_u03b1_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_motive_3225_, lean_object* v_l_3226_, lean_object* v_h__1_3227_, lean_object* v_h__2_3228_){
_start:
{
if (lean_obj_tag(v_l_3226_) == 0)
{
lean_object* v_size_3229_; lean_object* v_k_3230_; lean_object* v_v_3231_; lean_object* v_l_3232_; lean_object* v_r_3233_; lean_object* v___x_3234_; 
lean_dec(v_h__1_3227_);
v_size_3229_ = lean_ctor_get(v_l_3226_, 0);
lean_inc(v_size_3229_);
v_k_3230_ = lean_ctor_get(v_l_3226_, 1);
lean_inc(v_k_3230_);
v_v_3231_ = lean_ctor_get(v_l_3226_, 2);
lean_inc(v_v_3231_);
v_l_3232_ = lean_ctor_get(v_l_3226_, 3);
lean_inc(v_l_3232_);
v_r_3233_ = lean_ctor_get(v_l_3226_, 4);
lean_inc(v_r_3233_);
lean_dec_ref(v_l_3226_);
v___x_3234_ = lean_apply_5(v_h__2_3228_, v_size_3229_, v_k_3230_, v_v_3231_, v_l_3232_, v_r_3233_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec(v_h__2_3228_);
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_apply_1(v_h__1_3227_, v___x_3235_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR___redArg(lean_object* v_k_3237_, lean_object* v_v_3238_, lean_object* v_lk_3239_, lean_object* v_lv_3240_, lean_object* v_ll_3241_, lean_object* v_lr_3242_, lean_object* v_r_3243_){
_start:
{
lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3258_; 
if (lean_obj_tag(v_lr_3242_) == 0)
{
lean_object* v_size_3262_; 
v_size_3262_ = lean_ctor_get(v_lr_3242_, 0);
lean_inc(v_size_3262_);
v___y_3258_ = v_size_3262_;
goto v___jp_3257_;
}
else
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
v___y_3258_ = v___x_3263_;
goto v___jp_3257_;
}
v___jp_3244_:
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = lean_nat_mul(v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
v___x_3249_ = lean_nat_dec_lt(v___y_3245_, v___x_3248_);
lean_dec(v___x_3248_);
lean_dec(v___y_3245_);
if (v___x_3249_ == 0)
{
if (lean_obj_tag(v_lr_3242_) == 0)
{
lean_object* v_k_3250_; lean_object* v_v_3251_; lean_object* v_l_3252_; lean_object* v_r_3253_; lean_object* v___x_3254_; 
v_k_3250_ = lean_ctor_get(v_lr_3242_, 1);
lean_inc(v_k_3250_);
v_v_3251_ = lean_ctor_get(v_lr_3242_, 2);
lean_inc(v_v_3251_);
v_l_3252_ = lean_ctor_get(v_lr_3242_, 3);
lean_inc(v_l_3252_);
v_r_3253_ = lean_ctor_get(v_lr_3242_, 4);
lean_inc(v_r_3253_);
lean_dec_ref(v_lr_3242_);
v___x_3254_ = l_Std_DTreeMap_Internal_Impl_doubleR___redArg(v_k_3237_, v_v_3238_, v_lk_3239_, v_lv_3240_, v_ll_3241_, v_k_3250_, v_v_3251_, v_l_3252_, v_r_3253_, v_r_3243_);
return v___x_3254_;
}
else
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_DTreeMap_Internal_Impl_singleR___redArg(v_k_3237_, v_v_3238_, v_lk_3239_, v_lv_3240_, v_ll_3241_, v_lr_3242_, v_r_3243_);
return v___x_3255_;
}
}
else
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Std_DTreeMap_Internal_Impl_singleR___redArg(v_k_3237_, v_v_3238_, v_lk_3239_, v_lv_3240_, v_ll_3241_, v_lr_3242_, v_r_3243_);
return v___x_3256_;
}
}
v___jp_3257_:
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_unsigned_to_nat(2u);
if (lean_obj_tag(v_ll_3241_) == 0)
{
lean_object* v_size_3260_; 
v_size_3260_ = lean_ctor_get(v_ll_3241_, 0);
lean_inc(v_size_3260_);
v___y_3245_ = v___y_3258_;
v___y_3246_ = v___x_3259_;
v___y_3247_ = v_size_3260_;
goto v___jp_3244_;
}
else
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_unsigned_to_nat(0u);
v___y_3245_ = v___y_3258_;
v___y_3246_ = v___x_3259_;
v___y_3247_ = v___x_3261_;
goto v___jp_3244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR(lean_object* v_00_u03b1_3264_, lean_object* v_00_u03b2_3265_, lean_object* v_k_3266_, lean_object* v_v_3267_, lean_object* v_lk_3268_, lean_object* v_lv_3269_, lean_object* v_ll_3270_, lean_object* v_lr_3271_, lean_object* v_r_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Std_DTreeMap_Internal_Impl_rotateR___redArg(v_k_3266_, v_v_3267_, v_lk_3268_, v_lv_3269_, v_ll_3270_, v_lr_3271_, v_r_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098___redArg(lean_object* v_k_3274_, lean_object* v_v_3275_, lean_object* v_l_3276_, lean_object* v_r_3277_){
_start:
{
lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3302_; 
if (lean_obj_tag(v_l_3276_) == 0)
{
lean_object* v_size_3305_; 
v_size_3305_ = lean_ctor_get(v_l_3276_, 0);
lean_inc(v_size_3305_);
v___y_3302_ = v_size_3305_;
goto v___jp_3301_;
}
else
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_unsigned_to_nat(0u);
v___y_3302_ = v___x_3306_;
goto v___jp_3301_;
}
v___jp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3281_ = lean_nat_add(v___y_3279_, v___y_3280_);
v___x_3282_ = lean_unsigned_to_nat(1u);
v___x_3283_ = lean_nat_dec_le(v___x_3281_, v___x_3282_);
lean_dec(v___x_3281_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3284_ = lean_unsigned_to_nat(3u);
v___x_3285_ = lean_nat_mul(v___x_3284_, v___y_3279_);
v___x_3286_ = lean_nat_dec_lt(v___x_3285_, v___y_3280_);
lean_dec(v___x_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = lean_nat_mul(v___x_3284_, v___y_3280_);
lean_dec(v___y_3280_);
v___x_3288_ = lean_nat_dec_lt(v___x_3287_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec(v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3274_, v_v_3275_, v_l_3276_, v_r_3277_);
return v___x_3289_;
}
else
{
lean_object* v_k_3290_; lean_object* v_v_3291_; lean_object* v_l_3292_; lean_object* v_r_3293_; lean_object* v___x_3294_; 
v_k_3290_ = lean_ctor_get(v_l_3276_, 1);
lean_inc(v_k_3290_);
v_v_3291_ = lean_ctor_get(v_l_3276_, 2);
lean_inc(v_v_3291_);
v_l_3292_ = lean_ctor_get(v_l_3276_, 3);
lean_inc(v_l_3292_);
v_r_3293_ = lean_ctor_get(v_l_3276_, 4);
lean_inc(v_r_3293_);
lean_dec(v_l_3276_);
v___x_3294_ = l_Std_DTreeMap_Internal_Impl_rotateR___redArg(v_k_3274_, v_v_3275_, v_k_3290_, v_v_3291_, v_l_3292_, v_r_3293_, v_r_3277_);
return v___x_3294_;
}
}
else
{
lean_object* v_k_3295_; lean_object* v_v_3296_; lean_object* v_l_3297_; lean_object* v_r_3298_; lean_object* v___x_3299_; 
lean_dec(v___y_3280_);
lean_dec(v___y_3279_);
v_k_3295_ = lean_ctor_get(v_r_3277_, 1);
lean_inc(v_k_3295_);
v_v_3296_ = lean_ctor_get(v_r_3277_, 2);
lean_inc(v_v_3296_);
v_l_3297_ = lean_ctor_get(v_r_3277_, 3);
lean_inc(v_l_3297_);
v_r_3298_ = lean_ctor_get(v_r_3277_, 4);
lean_inc(v_r_3298_);
lean_dec(v_r_3277_);
v___x_3299_ = l_Std_DTreeMap_Internal_Impl_rotateL___redArg(v_k_3274_, v_v_3275_, v_l_3276_, v_k_3295_, v_v_3296_, v_l_3297_, v_r_3298_);
return v___x_3299_;
}
}
else
{
lean_object* v___x_3300_; 
lean_dec(v___y_3280_);
lean_dec(v___y_3279_);
v___x_3300_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3274_, v_v_3275_, v_l_3276_, v_r_3277_);
return v___x_3300_;
}
}
v___jp_3301_:
{
if (lean_obj_tag(v_r_3277_) == 0)
{
lean_object* v_size_3303_; 
v_size_3303_ = lean_ctor_get(v_r_3277_, 0);
lean_inc(v_size_3303_);
v___y_3279_ = v___y_3302_;
v___y_3280_ = v_size_3303_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_unsigned_to_nat(0u);
v___y_3279_ = v___y_3302_;
v___y_3280_ = v___x_3304_;
goto v___jp_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098(lean_object* v_00_u03b1_3307_, lean_object* v_00_u03b2_3308_, lean_object* v_k_3309_, lean_object* v_v_3310_, lean_object* v_l_3311_, lean_object* v_r_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Std_DTreeMap_Internal_Impl_balance_u2098___redArg(v_k_3309_, v_v_3310_, v_l_3311_, v_r_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter___redArg(lean_object* v_r_3314_, lean_object* v_h__1_3315_, lean_object* v_h__2_3316_, lean_object* v_h__3_3317_, lean_object* v_h__4_3318_, lean_object* v_h__5_3319_){
_start:
{
if (lean_obj_tag(v_r_3314_) == 0)
{
lean_object* v_l_3320_; 
lean_dec(v_h__1_3315_);
v_l_3320_ = lean_ctor_get(v_r_3314_, 3);
if (lean_obj_tag(v_l_3320_) == 0)
{
lean_object* v_r_3321_; 
lean_inc_ref(v_l_3320_);
lean_dec(v_h__3_3317_);
lean_dec(v_h__2_3316_);
v_r_3321_ = lean_ctor_get(v_r_3314_, 4);
if (lean_obj_tag(v_r_3321_) == 0)
{
lean_object* v_size_3322_; lean_object* v_k_3323_; lean_object* v_v_3324_; lean_object* v_size_3325_; lean_object* v_k_3326_; lean_object* v_v_3327_; lean_object* v_l_3328_; lean_object* v_r_3329_; lean_object* v_size_3330_; lean_object* v_k_3331_; lean_object* v_v_3332_; lean_object* v_l_3333_; lean_object* v_r_3334_; lean_object* v___x_3335_; 
lean_inc_ref(v_r_3321_);
lean_dec(v_h__4_3318_);
v_size_3322_ = lean_ctor_get(v_r_3314_, 0);
lean_inc(v_size_3322_);
v_k_3323_ = lean_ctor_get(v_r_3314_, 1);
lean_inc(v_k_3323_);
v_v_3324_ = lean_ctor_get(v_r_3314_, 2);
lean_inc(v_v_3324_);
lean_dec_ref(v_r_3314_);
v_size_3325_ = lean_ctor_get(v_l_3320_, 0);
lean_inc(v_size_3325_);
v_k_3326_ = lean_ctor_get(v_l_3320_, 1);
lean_inc(v_k_3326_);
v_v_3327_ = lean_ctor_get(v_l_3320_, 2);
lean_inc(v_v_3327_);
v_l_3328_ = lean_ctor_get(v_l_3320_, 3);
lean_inc(v_l_3328_);
v_r_3329_ = lean_ctor_get(v_l_3320_, 4);
lean_inc(v_r_3329_);
lean_dec_ref(v_l_3320_);
v_size_3330_ = lean_ctor_get(v_r_3321_, 0);
lean_inc(v_size_3330_);
v_k_3331_ = lean_ctor_get(v_r_3321_, 1);
lean_inc(v_k_3331_);
v_v_3332_ = lean_ctor_get(v_r_3321_, 2);
lean_inc(v_v_3332_);
v_l_3333_ = lean_ctor_get(v_r_3321_, 3);
lean_inc(v_l_3333_);
v_r_3334_ = lean_ctor_get(v_r_3321_, 4);
lean_inc(v_r_3334_);
lean_dec_ref(v_r_3321_);
v___x_3335_ = lean_apply_13(v_h__5_3319_, v_size_3322_, v_k_3323_, v_v_3324_, v_size_3325_, v_k_3326_, v_v_3327_, v_l_3328_, v_r_3329_, v_size_3330_, v_k_3331_, v_v_3332_, v_l_3333_, v_r_3334_);
return v___x_3335_;
}
else
{
lean_object* v_size_3336_; lean_object* v_k_3337_; lean_object* v_v_3338_; lean_object* v_size_3339_; lean_object* v_k_3340_; lean_object* v_v_3341_; lean_object* v_l_3342_; lean_object* v_r_3343_; lean_object* v___x_3344_; 
lean_dec(v_h__5_3319_);
v_size_3336_ = lean_ctor_get(v_r_3314_, 0);
lean_inc(v_size_3336_);
v_k_3337_ = lean_ctor_get(v_r_3314_, 1);
lean_inc(v_k_3337_);
v_v_3338_ = lean_ctor_get(v_r_3314_, 2);
lean_inc(v_v_3338_);
lean_dec_ref(v_r_3314_);
v_size_3339_ = lean_ctor_get(v_l_3320_, 0);
lean_inc(v_size_3339_);
v_k_3340_ = lean_ctor_get(v_l_3320_, 1);
lean_inc(v_k_3340_);
v_v_3341_ = lean_ctor_get(v_l_3320_, 2);
lean_inc(v_v_3341_);
v_l_3342_ = lean_ctor_get(v_l_3320_, 3);
lean_inc(v_l_3342_);
v_r_3343_ = lean_ctor_get(v_l_3320_, 4);
lean_inc(v_r_3343_);
lean_dec_ref(v_l_3320_);
v___x_3344_ = lean_apply_8(v_h__4_3318_, v_size_3336_, v_k_3337_, v_v_3338_, v_size_3339_, v_k_3340_, v_v_3341_, v_l_3342_, v_r_3343_);
return v___x_3344_;
}
}
else
{
lean_object* v_r_3345_; 
lean_dec(v_h__5_3319_);
lean_dec(v_h__4_3318_);
v_r_3345_ = lean_ctor_get(v_r_3314_, 4);
if (lean_obj_tag(v_r_3345_) == 0)
{
lean_object* v_size_3346_; lean_object* v_k_3347_; lean_object* v_v_3348_; lean_object* v_size_3349_; lean_object* v_k_3350_; lean_object* v_v_3351_; lean_object* v_l_3352_; lean_object* v_r_3353_; lean_object* v___x_3354_; 
lean_inc_ref(v_r_3345_);
lean_dec(v_h__2_3316_);
v_size_3346_ = lean_ctor_get(v_r_3314_, 0);
lean_inc(v_size_3346_);
v_k_3347_ = lean_ctor_get(v_r_3314_, 1);
lean_inc(v_k_3347_);
v_v_3348_ = lean_ctor_get(v_r_3314_, 2);
lean_inc(v_v_3348_);
lean_dec_ref(v_r_3314_);
v_size_3349_ = lean_ctor_get(v_r_3345_, 0);
lean_inc(v_size_3349_);
v_k_3350_ = lean_ctor_get(v_r_3345_, 1);
lean_inc(v_k_3350_);
v_v_3351_ = lean_ctor_get(v_r_3345_, 2);
lean_inc(v_v_3351_);
v_l_3352_ = lean_ctor_get(v_r_3345_, 3);
lean_inc(v_l_3352_);
v_r_3353_ = lean_ctor_get(v_r_3345_, 4);
lean_inc(v_r_3353_);
lean_dec_ref(v_r_3345_);
v___x_3354_ = lean_apply_8(v_h__3_3317_, v_size_3346_, v_k_3347_, v_v_3348_, v_size_3349_, v_k_3350_, v_v_3351_, v_l_3352_, v_r_3353_);
return v___x_3354_;
}
else
{
lean_object* v_size_3355_; lean_object* v_k_3356_; lean_object* v_v_3357_; lean_object* v___x_3358_; 
lean_dec(v_h__3_3317_);
v_size_3355_ = lean_ctor_get(v_r_3314_, 0);
lean_inc(v_size_3355_);
v_k_3356_ = lean_ctor_get(v_r_3314_, 1);
lean_inc(v_k_3356_);
v_v_3357_ = lean_ctor_get(v_r_3314_, 2);
lean_inc(v_v_3357_);
lean_dec_ref(v_r_3314_);
v___x_3358_ = lean_apply_3(v_h__2_3316_, v_size_3355_, v_k_3356_, v_v_3357_);
return v___x_3358_;
}
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec(v_h__5_3319_);
lean_dec(v_h__4_3318_);
lean_dec(v_h__3_3317_);
lean_dec(v_h__2_3316_);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_apply_1(v_h__1_3315_, v___x_3359_);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter(lean_object* v_00_u03b1_3361_, lean_object* v_00_u03b2_3362_, lean_object* v_motive_3363_, lean_object* v_r_3364_, lean_object* v_h__1_3365_, lean_object* v_h__2_3366_, lean_object* v_h__3_3367_, lean_object* v_h__4_3368_, lean_object* v_h__5_3369_){
_start:
{
if (lean_obj_tag(v_r_3364_) == 0)
{
lean_object* v_l_3370_; 
lean_dec(v_h__1_3365_);
v_l_3370_ = lean_ctor_get(v_r_3364_, 3);
if (lean_obj_tag(v_l_3370_) == 0)
{
lean_object* v_r_3371_; 
lean_inc_ref(v_l_3370_);
lean_dec(v_h__3_3367_);
lean_dec(v_h__2_3366_);
v_r_3371_ = lean_ctor_get(v_r_3364_, 4);
if (lean_obj_tag(v_r_3371_) == 0)
{
lean_object* v_size_3372_; lean_object* v_k_3373_; lean_object* v_v_3374_; lean_object* v_size_3375_; lean_object* v_k_3376_; lean_object* v_v_3377_; lean_object* v_l_3378_; lean_object* v_r_3379_; lean_object* v_size_3380_; lean_object* v_k_3381_; lean_object* v_v_3382_; lean_object* v_l_3383_; lean_object* v_r_3384_; lean_object* v___x_3385_; 
lean_inc_ref(v_r_3371_);
lean_dec(v_h__4_3368_);
v_size_3372_ = lean_ctor_get(v_r_3364_, 0);
lean_inc(v_size_3372_);
v_k_3373_ = lean_ctor_get(v_r_3364_, 1);
lean_inc(v_k_3373_);
v_v_3374_ = lean_ctor_get(v_r_3364_, 2);
lean_inc(v_v_3374_);
lean_dec_ref(v_r_3364_);
v_size_3375_ = lean_ctor_get(v_l_3370_, 0);
lean_inc(v_size_3375_);
v_k_3376_ = lean_ctor_get(v_l_3370_, 1);
lean_inc(v_k_3376_);
v_v_3377_ = lean_ctor_get(v_l_3370_, 2);
lean_inc(v_v_3377_);
v_l_3378_ = lean_ctor_get(v_l_3370_, 3);
lean_inc(v_l_3378_);
v_r_3379_ = lean_ctor_get(v_l_3370_, 4);
lean_inc(v_r_3379_);
lean_dec_ref(v_l_3370_);
v_size_3380_ = lean_ctor_get(v_r_3371_, 0);
lean_inc(v_size_3380_);
v_k_3381_ = lean_ctor_get(v_r_3371_, 1);
lean_inc(v_k_3381_);
v_v_3382_ = lean_ctor_get(v_r_3371_, 2);
lean_inc(v_v_3382_);
v_l_3383_ = lean_ctor_get(v_r_3371_, 3);
lean_inc(v_l_3383_);
v_r_3384_ = lean_ctor_get(v_r_3371_, 4);
lean_inc(v_r_3384_);
lean_dec_ref(v_r_3371_);
v___x_3385_ = lean_apply_13(v_h__5_3369_, v_size_3372_, v_k_3373_, v_v_3374_, v_size_3375_, v_k_3376_, v_v_3377_, v_l_3378_, v_r_3379_, v_size_3380_, v_k_3381_, v_v_3382_, v_l_3383_, v_r_3384_);
return v___x_3385_;
}
else
{
lean_object* v_size_3386_; lean_object* v_k_3387_; lean_object* v_v_3388_; lean_object* v_size_3389_; lean_object* v_k_3390_; lean_object* v_v_3391_; lean_object* v_l_3392_; lean_object* v_r_3393_; lean_object* v___x_3394_; 
lean_dec(v_h__5_3369_);
v_size_3386_ = lean_ctor_get(v_r_3364_, 0);
lean_inc(v_size_3386_);
v_k_3387_ = lean_ctor_get(v_r_3364_, 1);
lean_inc(v_k_3387_);
v_v_3388_ = lean_ctor_get(v_r_3364_, 2);
lean_inc(v_v_3388_);
lean_dec_ref(v_r_3364_);
v_size_3389_ = lean_ctor_get(v_l_3370_, 0);
lean_inc(v_size_3389_);
v_k_3390_ = lean_ctor_get(v_l_3370_, 1);
lean_inc(v_k_3390_);
v_v_3391_ = lean_ctor_get(v_l_3370_, 2);
lean_inc(v_v_3391_);
v_l_3392_ = lean_ctor_get(v_l_3370_, 3);
lean_inc(v_l_3392_);
v_r_3393_ = lean_ctor_get(v_l_3370_, 4);
lean_inc(v_r_3393_);
lean_dec_ref(v_l_3370_);
v___x_3394_ = lean_apply_8(v_h__4_3368_, v_size_3386_, v_k_3387_, v_v_3388_, v_size_3389_, v_k_3390_, v_v_3391_, v_l_3392_, v_r_3393_);
return v___x_3394_;
}
}
else
{
lean_object* v_r_3395_; 
lean_dec(v_h__5_3369_);
lean_dec(v_h__4_3368_);
v_r_3395_ = lean_ctor_get(v_r_3364_, 4);
if (lean_obj_tag(v_r_3395_) == 0)
{
lean_object* v_size_3396_; lean_object* v_k_3397_; lean_object* v_v_3398_; lean_object* v_size_3399_; lean_object* v_k_3400_; lean_object* v_v_3401_; lean_object* v_l_3402_; lean_object* v_r_3403_; lean_object* v___x_3404_; 
lean_inc_ref(v_r_3395_);
lean_dec(v_h__2_3366_);
v_size_3396_ = lean_ctor_get(v_r_3364_, 0);
lean_inc(v_size_3396_);
v_k_3397_ = lean_ctor_get(v_r_3364_, 1);
lean_inc(v_k_3397_);
v_v_3398_ = lean_ctor_get(v_r_3364_, 2);
lean_inc(v_v_3398_);
lean_dec_ref(v_r_3364_);
v_size_3399_ = lean_ctor_get(v_r_3395_, 0);
lean_inc(v_size_3399_);
v_k_3400_ = lean_ctor_get(v_r_3395_, 1);
lean_inc(v_k_3400_);
v_v_3401_ = lean_ctor_get(v_r_3395_, 2);
lean_inc(v_v_3401_);
v_l_3402_ = lean_ctor_get(v_r_3395_, 3);
lean_inc(v_l_3402_);
v_r_3403_ = lean_ctor_get(v_r_3395_, 4);
lean_inc(v_r_3403_);
lean_dec_ref(v_r_3395_);
v___x_3404_ = lean_apply_8(v_h__3_3367_, v_size_3396_, v_k_3397_, v_v_3398_, v_size_3399_, v_k_3400_, v_v_3401_, v_l_3402_, v_r_3403_);
return v___x_3404_;
}
else
{
lean_object* v_size_3405_; lean_object* v_k_3406_; lean_object* v_v_3407_; lean_object* v___x_3408_; 
lean_dec(v_h__3_3367_);
v_size_3405_ = lean_ctor_get(v_r_3364_, 0);
lean_inc(v_size_3405_);
v_k_3406_ = lean_ctor_get(v_r_3364_, 1);
lean_inc(v_k_3406_);
v_v_3407_ = lean_ctor_get(v_r_3364_, 2);
lean_inc(v_v_3407_);
lean_dec_ref(v_r_3364_);
v___x_3408_ = lean_apply_3(v_h__2_3366_, v_size_3405_, v_k_3406_, v_v_3407_);
return v___x_3408_;
}
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_dec(v_h__5_3369_);
lean_dec(v_h__4_3368_);
lean_dec(v_h__3_3367_);
lean_dec(v_h__2_3366_);
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_apply_1(v_h__1_3365_, v___x_3409_);
return v___x_3410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter___redArg(lean_object* v_ll_3411_, lean_object* v_lr_3412_, lean_object* v_h__1_3413_, lean_object* v_h__2_3414_, lean_object* v_h__3_3415_, lean_object* v_h__4_3416_){
_start:
{
if (lean_obj_tag(v_ll_3411_) == 0)
{
lean_dec(v_h__2_3414_);
lean_dec(v_h__1_3413_);
if (lean_obj_tag(v_lr_3412_) == 0)
{
lean_object* v_size_3417_; lean_object* v_k_3418_; lean_object* v_v_3419_; lean_object* v_l_3420_; lean_object* v_r_3421_; lean_object* v_size_3422_; lean_object* v_k_3423_; lean_object* v_v_3424_; lean_object* v_l_3425_; lean_object* v_r_3426_; lean_object* v___x_3427_; 
lean_dec(v_h__3_3415_);
v_size_3417_ = lean_ctor_get(v_ll_3411_, 0);
lean_inc(v_size_3417_);
v_k_3418_ = lean_ctor_get(v_ll_3411_, 1);
lean_inc(v_k_3418_);
v_v_3419_ = lean_ctor_get(v_ll_3411_, 2);
lean_inc(v_v_3419_);
v_l_3420_ = lean_ctor_get(v_ll_3411_, 3);
lean_inc(v_l_3420_);
v_r_3421_ = lean_ctor_get(v_ll_3411_, 4);
lean_inc(v_r_3421_);
lean_dec_ref(v_ll_3411_);
v_size_3422_ = lean_ctor_get(v_lr_3412_, 0);
lean_inc(v_size_3422_);
v_k_3423_ = lean_ctor_get(v_lr_3412_, 1);
lean_inc(v_k_3423_);
v_v_3424_ = lean_ctor_get(v_lr_3412_, 2);
lean_inc(v_v_3424_);
v_l_3425_ = lean_ctor_get(v_lr_3412_, 3);
lean_inc(v_l_3425_);
v_r_3426_ = lean_ctor_get(v_lr_3412_, 4);
lean_inc(v_r_3426_);
lean_dec_ref(v_lr_3412_);
v___x_3427_ = lean_apply_10(v_h__4_3416_, v_size_3417_, v_k_3418_, v_v_3419_, v_l_3420_, v_r_3421_, v_size_3422_, v_k_3423_, v_v_3424_, v_l_3425_, v_r_3426_);
return v___x_3427_;
}
else
{
lean_object* v_size_3428_; lean_object* v_k_3429_; lean_object* v_v_3430_; lean_object* v_l_3431_; lean_object* v_r_3432_; lean_object* v___x_3433_; 
lean_dec(v_h__4_3416_);
v_size_3428_ = lean_ctor_get(v_ll_3411_, 0);
lean_inc(v_size_3428_);
v_k_3429_ = lean_ctor_get(v_ll_3411_, 1);
lean_inc(v_k_3429_);
v_v_3430_ = lean_ctor_get(v_ll_3411_, 2);
lean_inc(v_v_3430_);
v_l_3431_ = lean_ctor_get(v_ll_3411_, 3);
lean_inc(v_l_3431_);
v_r_3432_ = lean_ctor_get(v_ll_3411_, 4);
lean_inc(v_r_3432_);
lean_dec_ref(v_ll_3411_);
v___x_3433_ = lean_apply_5(v_h__3_3415_, v_size_3428_, v_k_3429_, v_v_3430_, v_l_3431_, v_r_3432_);
return v___x_3433_;
}
}
else
{
lean_dec(v_h__4_3416_);
lean_dec(v_h__3_3415_);
if (lean_obj_tag(v_lr_3412_) == 0)
{
lean_object* v_size_3434_; lean_object* v_k_3435_; lean_object* v_v_3436_; lean_object* v_l_3437_; lean_object* v_r_3438_; lean_object* v___x_3439_; 
lean_dec(v_h__1_3413_);
v_size_3434_ = lean_ctor_get(v_lr_3412_, 0);
lean_inc(v_size_3434_);
v_k_3435_ = lean_ctor_get(v_lr_3412_, 1);
lean_inc(v_k_3435_);
v_v_3436_ = lean_ctor_get(v_lr_3412_, 2);
lean_inc(v_v_3436_);
v_l_3437_ = lean_ctor_get(v_lr_3412_, 3);
lean_inc(v_l_3437_);
v_r_3438_ = lean_ctor_get(v_lr_3412_, 4);
lean_inc(v_r_3438_);
lean_dec_ref(v_lr_3412_);
v___x_3439_ = lean_apply_5(v_h__2_3414_, v_size_3434_, v_k_3435_, v_v_3436_, v_l_3437_, v_r_3438_);
return v___x_3439_;
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec(v_h__2_3414_);
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_apply_1(v_h__1_3413_, v___x_3440_);
return v___x_3441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter(lean_object* v_00_u03b1_3442_, lean_object* v_00_u03b2_3443_, lean_object* v_motive_3444_, lean_object* v_ll_3445_, lean_object* v_lr_3446_, lean_object* v_h__1_3447_, lean_object* v_h__2_3448_, lean_object* v_h__3_3449_, lean_object* v_h__4_3450_){
_start:
{
if (lean_obj_tag(v_ll_3445_) == 0)
{
lean_dec(v_h__2_3448_);
lean_dec(v_h__1_3447_);
if (lean_obj_tag(v_lr_3446_) == 0)
{
lean_object* v_size_3451_; lean_object* v_k_3452_; lean_object* v_v_3453_; lean_object* v_l_3454_; lean_object* v_r_3455_; lean_object* v_size_3456_; lean_object* v_k_3457_; lean_object* v_v_3458_; lean_object* v_l_3459_; lean_object* v_r_3460_; lean_object* v___x_3461_; 
lean_dec(v_h__3_3449_);
v_size_3451_ = lean_ctor_get(v_ll_3445_, 0);
lean_inc(v_size_3451_);
v_k_3452_ = lean_ctor_get(v_ll_3445_, 1);
lean_inc(v_k_3452_);
v_v_3453_ = lean_ctor_get(v_ll_3445_, 2);
lean_inc(v_v_3453_);
v_l_3454_ = lean_ctor_get(v_ll_3445_, 3);
lean_inc(v_l_3454_);
v_r_3455_ = lean_ctor_get(v_ll_3445_, 4);
lean_inc(v_r_3455_);
lean_dec_ref(v_ll_3445_);
v_size_3456_ = lean_ctor_get(v_lr_3446_, 0);
lean_inc(v_size_3456_);
v_k_3457_ = lean_ctor_get(v_lr_3446_, 1);
lean_inc(v_k_3457_);
v_v_3458_ = lean_ctor_get(v_lr_3446_, 2);
lean_inc(v_v_3458_);
v_l_3459_ = lean_ctor_get(v_lr_3446_, 3);
lean_inc(v_l_3459_);
v_r_3460_ = lean_ctor_get(v_lr_3446_, 4);
lean_inc(v_r_3460_);
lean_dec_ref(v_lr_3446_);
v___x_3461_ = lean_apply_10(v_h__4_3450_, v_size_3451_, v_k_3452_, v_v_3453_, v_l_3454_, v_r_3455_, v_size_3456_, v_k_3457_, v_v_3458_, v_l_3459_, v_r_3460_);
return v___x_3461_;
}
else
{
lean_object* v_size_3462_; lean_object* v_k_3463_; lean_object* v_v_3464_; lean_object* v_l_3465_; lean_object* v_r_3466_; lean_object* v___x_3467_; 
lean_dec(v_h__4_3450_);
v_size_3462_ = lean_ctor_get(v_ll_3445_, 0);
lean_inc(v_size_3462_);
v_k_3463_ = lean_ctor_get(v_ll_3445_, 1);
lean_inc(v_k_3463_);
v_v_3464_ = lean_ctor_get(v_ll_3445_, 2);
lean_inc(v_v_3464_);
v_l_3465_ = lean_ctor_get(v_ll_3445_, 3);
lean_inc(v_l_3465_);
v_r_3466_ = lean_ctor_get(v_ll_3445_, 4);
lean_inc(v_r_3466_);
lean_dec_ref(v_ll_3445_);
v___x_3467_ = lean_apply_5(v_h__3_3449_, v_size_3462_, v_k_3463_, v_v_3464_, v_l_3465_, v_r_3466_);
return v___x_3467_;
}
}
else
{
lean_dec(v_h__4_3450_);
lean_dec(v_h__3_3449_);
if (lean_obj_tag(v_lr_3446_) == 0)
{
lean_object* v_size_3468_; lean_object* v_k_3469_; lean_object* v_v_3470_; lean_object* v_l_3471_; lean_object* v_r_3472_; lean_object* v___x_3473_; 
lean_dec(v_h__1_3447_);
v_size_3468_ = lean_ctor_get(v_lr_3446_, 0);
lean_inc(v_size_3468_);
v_k_3469_ = lean_ctor_get(v_lr_3446_, 1);
lean_inc(v_k_3469_);
v_v_3470_ = lean_ctor_get(v_lr_3446_, 2);
lean_inc(v_v_3470_);
v_l_3471_ = lean_ctor_get(v_lr_3446_, 3);
lean_inc(v_l_3471_);
v_r_3472_ = lean_ctor_get(v_lr_3446_, 4);
lean_inc(v_r_3472_);
lean_dec_ref(v_lr_3446_);
v___x_3473_ = lean_apply_5(v_h__2_3448_, v_size_3468_, v_k_3469_, v_v_3470_, v_l_3471_, v_r_3472_);
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec(v_h__2_3448_);
v___x_3474_ = lean_box(0);
v___x_3475_ = lean_apply_1(v_h__1_3447_, v___x_3474_);
return v___x_3475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter___redArg(lean_object* v_ll_3476_, lean_object* v_lr_3477_, lean_object* v_h__1_3478_, lean_object* v_h__2_3479_, lean_object* v_h__3_3480_){
_start:
{
if (lean_obj_tag(v_ll_3476_) == 0)
{
lean_dec(v_h__3_3480_);
if (lean_obj_tag(v_lr_3477_) == 0)
{
lean_object* v_size_3481_; lean_object* v_k_3482_; lean_object* v_v_3483_; lean_object* v_l_3484_; lean_object* v_r_3485_; lean_object* v_size_3486_; lean_object* v_k_3487_; lean_object* v_v_3488_; lean_object* v_l_3489_; lean_object* v_r_3490_; lean_object* v___x_3491_; 
lean_dec(v_h__2_3479_);
v_size_3481_ = lean_ctor_get(v_ll_3476_, 0);
lean_inc(v_size_3481_);
v_k_3482_ = lean_ctor_get(v_ll_3476_, 1);
lean_inc(v_k_3482_);
v_v_3483_ = lean_ctor_get(v_ll_3476_, 2);
lean_inc(v_v_3483_);
v_l_3484_ = lean_ctor_get(v_ll_3476_, 3);
lean_inc(v_l_3484_);
v_r_3485_ = lean_ctor_get(v_ll_3476_, 4);
lean_inc(v_r_3485_);
lean_dec_ref(v_ll_3476_);
v_size_3486_ = lean_ctor_get(v_lr_3477_, 0);
lean_inc(v_size_3486_);
v_k_3487_ = lean_ctor_get(v_lr_3477_, 1);
lean_inc(v_k_3487_);
v_v_3488_ = lean_ctor_get(v_lr_3477_, 2);
lean_inc(v_v_3488_);
v_l_3489_ = lean_ctor_get(v_lr_3477_, 3);
lean_inc(v_l_3489_);
v_r_3490_ = lean_ctor_get(v_lr_3477_, 4);
lean_inc(v_r_3490_);
lean_dec_ref(v_lr_3477_);
v___x_3491_ = lean_apply_10(v_h__1_3478_, v_size_3481_, v_k_3482_, v_v_3483_, v_l_3484_, v_r_3485_, v_size_3486_, v_k_3487_, v_v_3488_, v_l_3489_, v_r_3490_);
return v___x_3491_;
}
else
{
lean_object* v_size_3492_; lean_object* v_k_3493_; lean_object* v_v_3494_; lean_object* v_l_3495_; lean_object* v_r_3496_; lean_object* v___x_3497_; 
lean_dec(v_h__1_3478_);
v_size_3492_ = lean_ctor_get(v_ll_3476_, 0);
lean_inc(v_size_3492_);
v_k_3493_ = lean_ctor_get(v_ll_3476_, 1);
lean_inc(v_k_3493_);
v_v_3494_ = lean_ctor_get(v_ll_3476_, 2);
lean_inc(v_v_3494_);
v_l_3495_ = lean_ctor_get(v_ll_3476_, 3);
lean_inc(v_l_3495_);
v_r_3496_ = lean_ctor_get(v_ll_3476_, 4);
lean_inc(v_r_3496_);
lean_dec_ref(v_ll_3476_);
v___x_3497_ = lean_apply_5(v_h__2_3479_, v_size_3492_, v_k_3493_, v_v_3494_, v_l_3495_, v_r_3496_);
return v___x_3497_;
}
}
else
{
lean_object* v___x_3498_; 
lean_dec(v_h__2_3479_);
lean_dec(v_h__1_3478_);
v___x_3498_ = lean_apply_1(v_h__3_3480_, v_lr_3477_);
return v___x_3498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter(lean_object* v_00_u03b1_3499_, lean_object* v_00_u03b2_3500_, lean_object* v_motive_3501_, lean_object* v_ll_3502_, lean_object* v_lr_3503_, lean_object* v_h__1_3504_, lean_object* v_h__2_3505_, lean_object* v_h__3_3506_){
_start:
{
if (lean_obj_tag(v_ll_3502_) == 0)
{
lean_dec(v_h__3_3506_);
if (lean_obj_tag(v_lr_3503_) == 0)
{
lean_object* v_size_3507_; lean_object* v_k_3508_; lean_object* v_v_3509_; lean_object* v_l_3510_; lean_object* v_r_3511_; lean_object* v_size_3512_; lean_object* v_k_3513_; lean_object* v_v_3514_; lean_object* v_l_3515_; lean_object* v_r_3516_; lean_object* v___x_3517_; 
lean_dec(v_h__2_3505_);
v_size_3507_ = lean_ctor_get(v_ll_3502_, 0);
lean_inc(v_size_3507_);
v_k_3508_ = lean_ctor_get(v_ll_3502_, 1);
lean_inc(v_k_3508_);
v_v_3509_ = lean_ctor_get(v_ll_3502_, 2);
lean_inc(v_v_3509_);
v_l_3510_ = lean_ctor_get(v_ll_3502_, 3);
lean_inc(v_l_3510_);
v_r_3511_ = lean_ctor_get(v_ll_3502_, 4);
lean_inc(v_r_3511_);
lean_dec_ref(v_ll_3502_);
v_size_3512_ = lean_ctor_get(v_lr_3503_, 0);
lean_inc(v_size_3512_);
v_k_3513_ = lean_ctor_get(v_lr_3503_, 1);
lean_inc(v_k_3513_);
v_v_3514_ = lean_ctor_get(v_lr_3503_, 2);
lean_inc(v_v_3514_);
v_l_3515_ = lean_ctor_get(v_lr_3503_, 3);
lean_inc(v_l_3515_);
v_r_3516_ = lean_ctor_get(v_lr_3503_, 4);
lean_inc(v_r_3516_);
lean_dec_ref(v_lr_3503_);
v___x_3517_ = lean_apply_10(v_h__1_3504_, v_size_3507_, v_k_3508_, v_v_3509_, v_l_3510_, v_r_3511_, v_size_3512_, v_k_3513_, v_v_3514_, v_l_3515_, v_r_3516_);
return v___x_3517_;
}
else
{
lean_object* v_size_3518_; lean_object* v_k_3519_; lean_object* v_v_3520_; lean_object* v_l_3521_; lean_object* v_r_3522_; lean_object* v___x_3523_; 
lean_dec(v_h__1_3504_);
v_size_3518_ = lean_ctor_get(v_ll_3502_, 0);
lean_inc(v_size_3518_);
v_k_3519_ = lean_ctor_get(v_ll_3502_, 1);
lean_inc(v_k_3519_);
v_v_3520_ = lean_ctor_get(v_ll_3502_, 2);
lean_inc(v_v_3520_);
v_l_3521_ = lean_ctor_get(v_ll_3502_, 3);
lean_inc(v_l_3521_);
v_r_3522_ = lean_ctor_get(v_ll_3502_, 4);
lean_inc(v_r_3522_);
lean_dec_ref(v_ll_3502_);
v___x_3523_ = lean_apply_5(v_h__2_3505_, v_size_3518_, v_k_3519_, v_v_3520_, v_l_3521_, v_r_3522_);
return v___x_3523_;
}
}
else
{
lean_object* v___x_3524_; 
lean_dec(v_h__2_3505_);
lean_dec(v_h__1_3504_);
v___x_3524_ = lean_apply_1(v_h__3_3506_, v_lr_3503_);
return v___x_3524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___redArg(lean_object* v_r_3525_, lean_object* v_h__1_3526_, lean_object* v_h__2_3527_){
_start:
{
if (lean_obj_tag(v_r_3525_) == 0)
{
lean_object* v_size_3528_; lean_object* v_k_3529_; lean_object* v_v_3530_; lean_object* v_l_3531_; lean_object* v_r_3532_; lean_object* v___x_3533_; 
lean_dec(v_h__1_3526_);
v_size_3528_ = lean_ctor_get(v_r_3525_, 0);
lean_inc(v_size_3528_);
v_k_3529_ = lean_ctor_get(v_r_3525_, 1);
lean_inc(v_k_3529_);
v_v_3530_ = lean_ctor_get(v_r_3525_, 2);
lean_inc(v_v_3530_);
v_l_3531_ = lean_ctor_get(v_r_3525_, 3);
lean_inc(v_l_3531_);
v_r_3532_ = lean_ctor_get(v_r_3525_, 4);
lean_inc(v_r_3532_);
lean_dec_ref(v_r_3525_);
v___x_3533_ = lean_apply_7(v_h__2_3527_, v_size_3528_, v_k_3529_, v_v_3530_, v_l_3531_, v_r_3532_, lean_box(0), lean_box(0));
return v___x_3533_;
}
else
{
lean_object* v___x_3534_; 
lean_dec(v_h__2_3527_);
v___x_3534_ = lean_apply_2(v_h__1_3526_, lean_box(0), lean_box(0));
return v___x_3534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter(lean_object* v_00_u03b1_3535_, lean_object* v_00_u03b2_3536_, lean_object* v_l_3537_, lean_object* v_motive_3538_, lean_object* v_r_3539_, lean_object* v_hrb_3540_, lean_object* v_hlr_3541_, lean_object* v_h__1_3542_, lean_object* v_h__2_3543_){
_start:
{
if (lean_obj_tag(v_r_3539_) == 0)
{
lean_object* v_size_3544_; lean_object* v_k_3545_; lean_object* v_v_3546_; lean_object* v_l_3547_; lean_object* v_r_3548_; lean_object* v___x_3549_; 
lean_dec(v_h__1_3542_);
v_size_3544_ = lean_ctor_get(v_r_3539_, 0);
lean_inc(v_size_3544_);
v_k_3545_ = lean_ctor_get(v_r_3539_, 1);
lean_inc(v_k_3545_);
v_v_3546_ = lean_ctor_get(v_r_3539_, 2);
lean_inc(v_v_3546_);
v_l_3547_ = lean_ctor_get(v_r_3539_, 3);
lean_inc(v_l_3547_);
v_r_3548_ = lean_ctor_get(v_r_3539_, 4);
lean_inc(v_r_3548_);
lean_dec_ref(v_r_3539_);
v___x_3549_ = lean_apply_7(v_h__2_3543_, v_size_3544_, v_k_3545_, v_v_3546_, v_l_3547_, v_r_3548_, lean_box(0), lean_box(0));
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; 
lean_dec(v_h__2_3543_);
v___x_3550_ = lean_apply_2(v_h__1_3542_, lean_box(0), lean_box(0));
return v___x_3550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___boxed(lean_object* v_00_u03b1_3551_, lean_object* v_00_u03b2_3552_, lean_object* v_l_3553_, lean_object* v_motive_3554_, lean_object* v_r_3555_, lean_object* v_hrb_3556_, lean_object* v_hlr_3557_, lean_object* v_h__1_3558_, lean_object* v_h__2_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter(v_00_u03b1_3551_, v_00_u03b2_3552_, v_l_3553_, v_motive_3554_, v_r_3555_, v_hrb_3556_, v_hlr_3557_, v_h__1_3558_, v_h__2_3559_);
lean_dec(v_l_3553_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter___redArg(lean_object* v_l_3561_, lean_object* v_h__1_3562_, lean_object* v_h__2_3563_, lean_object* v_h__3_3564_, lean_object* v_h__4_3565_, lean_object* v_h__5_3566_){
_start:
{
if (lean_obj_tag(v_l_3561_) == 0)
{
lean_object* v_l_3567_; 
lean_dec(v_h__1_3562_);
v_l_3567_ = lean_ctor_get(v_l_3561_, 3);
if (lean_obj_tag(v_l_3567_) == 0)
{
lean_object* v_r_3568_; 
lean_inc_ref(v_l_3567_);
lean_dec(v_h__3_3564_);
lean_dec(v_h__2_3563_);
v_r_3568_ = lean_ctor_get(v_l_3561_, 4);
if (lean_obj_tag(v_r_3568_) == 0)
{
lean_object* v_size_3569_; lean_object* v_k_3570_; lean_object* v_v_3571_; lean_object* v_size_3572_; lean_object* v_k_3573_; lean_object* v_v_3574_; lean_object* v_l_3575_; lean_object* v_r_3576_; lean_object* v_size_3577_; lean_object* v_k_3578_; lean_object* v_v_3579_; lean_object* v_l_3580_; lean_object* v_r_3581_; lean_object* v___x_3582_; 
lean_inc_ref(v_r_3568_);
lean_dec(v_h__4_3565_);
v_size_3569_ = lean_ctor_get(v_l_3561_, 0);
lean_inc(v_size_3569_);
v_k_3570_ = lean_ctor_get(v_l_3561_, 1);
lean_inc(v_k_3570_);
v_v_3571_ = lean_ctor_get(v_l_3561_, 2);
lean_inc(v_v_3571_);
lean_dec_ref(v_l_3561_);
v_size_3572_ = lean_ctor_get(v_l_3567_, 0);
lean_inc(v_size_3572_);
v_k_3573_ = lean_ctor_get(v_l_3567_, 1);
lean_inc(v_k_3573_);
v_v_3574_ = lean_ctor_get(v_l_3567_, 2);
lean_inc(v_v_3574_);
v_l_3575_ = lean_ctor_get(v_l_3567_, 3);
lean_inc(v_l_3575_);
v_r_3576_ = lean_ctor_get(v_l_3567_, 4);
lean_inc(v_r_3576_);
lean_dec_ref(v_l_3567_);
v_size_3577_ = lean_ctor_get(v_r_3568_, 0);
lean_inc(v_size_3577_);
v_k_3578_ = lean_ctor_get(v_r_3568_, 1);
lean_inc(v_k_3578_);
v_v_3579_ = lean_ctor_get(v_r_3568_, 2);
lean_inc(v_v_3579_);
v_l_3580_ = lean_ctor_get(v_r_3568_, 3);
lean_inc(v_l_3580_);
v_r_3581_ = lean_ctor_get(v_r_3568_, 4);
lean_inc(v_r_3581_);
lean_dec_ref(v_r_3568_);
v___x_3582_ = lean_apply_15(v_h__5_3566_, v_size_3569_, v_k_3570_, v_v_3571_, v_size_3572_, v_k_3573_, v_v_3574_, v_l_3575_, v_r_3576_, v_size_3577_, v_k_3578_, v_v_3579_, v_l_3580_, v_r_3581_, lean_box(0), lean_box(0));
return v___x_3582_;
}
else
{
lean_object* v_size_3583_; lean_object* v_k_3584_; lean_object* v_v_3585_; lean_object* v_size_3586_; lean_object* v_k_3587_; lean_object* v_v_3588_; lean_object* v_l_3589_; lean_object* v_r_3590_; lean_object* v___x_3591_; 
lean_dec(v_h__5_3566_);
v_size_3583_ = lean_ctor_get(v_l_3561_, 0);
lean_inc(v_size_3583_);
v_k_3584_ = lean_ctor_get(v_l_3561_, 1);
lean_inc(v_k_3584_);
v_v_3585_ = lean_ctor_get(v_l_3561_, 2);
lean_inc(v_v_3585_);
lean_dec_ref(v_l_3561_);
v_size_3586_ = lean_ctor_get(v_l_3567_, 0);
lean_inc(v_size_3586_);
v_k_3587_ = lean_ctor_get(v_l_3567_, 1);
lean_inc(v_k_3587_);
v_v_3588_ = lean_ctor_get(v_l_3567_, 2);
lean_inc(v_v_3588_);
v_l_3589_ = lean_ctor_get(v_l_3567_, 3);
lean_inc(v_l_3589_);
v_r_3590_ = lean_ctor_get(v_l_3567_, 4);
lean_inc(v_r_3590_);
lean_dec_ref(v_l_3567_);
v___x_3591_ = lean_apply_10(v_h__4_3565_, v_size_3583_, v_k_3584_, v_v_3585_, v_size_3586_, v_k_3587_, v_v_3588_, v_l_3589_, v_r_3590_, lean_box(0), lean_box(0));
return v___x_3591_;
}
}
else
{
lean_object* v_r_3592_; 
lean_dec(v_h__5_3566_);
lean_dec(v_h__4_3565_);
v_r_3592_ = lean_ctor_get(v_l_3561_, 4);
if (lean_obj_tag(v_r_3592_) == 0)
{
lean_object* v_size_3593_; lean_object* v_k_3594_; lean_object* v_v_3595_; lean_object* v_size_3596_; lean_object* v_k_3597_; lean_object* v_v_3598_; lean_object* v_l_3599_; lean_object* v_r_3600_; lean_object* v___x_3601_; 
lean_inc_ref(v_r_3592_);
lean_dec(v_h__2_3563_);
v_size_3593_ = lean_ctor_get(v_l_3561_, 0);
lean_inc(v_size_3593_);
v_k_3594_ = lean_ctor_get(v_l_3561_, 1);
lean_inc(v_k_3594_);
v_v_3595_ = lean_ctor_get(v_l_3561_, 2);
lean_inc(v_v_3595_);
lean_dec_ref(v_l_3561_);
v_size_3596_ = lean_ctor_get(v_r_3592_, 0);
lean_inc(v_size_3596_);
v_k_3597_ = lean_ctor_get(v_r_3592_, 1);
lean_inc(v_k_3597_);
v_v_3598_ = lean_ctor_get(v_r_3592_, 2);
lean_inc(v_v_3598_);
v_l_3599_ = lean_ctor_get(v_r_3592_, 3);
lean_inc(v_l_3599_);
v_r_3600_ = lean_ctor_get(v_r_3592_, 4);
lean_inc(v_r_3600_);
lean_dec_ref(v_r_3592_);
v___x_3601_ = lean_apply_10(v_h__3_3564_, v_size_3593_, v_k_3594_, v_v_3595_, v_size_3596_, v_k_3597_, v_v_3598_, v_l_3599_, v_r_3600_, lean_box(0), lean_box(0));
return v___x_3601_;
}
else
{
lean_object* v_size_3602_; lean_object* v_k_3603_; lean_object* v_v_3604_; lean_object* v___x_3605_; 
lean_dec(v_h__3_3564_);
v_size_3602_ = lean_ctor_get(v_l_3561_, 0);
lean_inc(v_size_3602_);
v_k_3603_ = lean_ctor_get(v_l_3561_, 1);
lean_inc(v_k_3603_);
v_v_3604_ = lean_ctor_get(v_l_3561_, 2);
lean_inc(v_v_3604_);
lean_dec_ref(v_l_3561_);
v___x_3605_ = lean_apply_5(v_h__2_3563_, v_size_3602_, v_k_3603_, v_v_3604_, lean_box(0), lean_box(0));
return v___x_3605_;
}
}
}
else
{
lean_object* v___x_3606_; 
lean_dec(v_h__5_3566_);
lean_dec(v_h__4_3565_);
lean_dec(v_h__3_3564_);
lean_dec(v_h__2_3563_);
v___x_3606_ = lean_apply_2(v_h__1_3562_, lean_box(0), lean_box(0));
return v___x_3606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter(lean_object* v_00_u03b1_3607_, lean_object* v_00_u03b2_3608_, lean_object* v_motive_3609_, lean_object* v_l_3610_, lean_object* v_hlb_3611_, lean_object* v_hlr_3612_, lean_object* v_h__1_3613_, lean_object* v_h__2_3614_, lean_object* v_h__3_3615_, lean_object* v_h__4_3616_, lean_object* v_h__5_3617_){
_start:
{
if (lean_obj_tag(v_l_3610_) == 0)
{
lean_object* v_l_3618_; 
lean_dec(v_h__1_3613_);
v_l_3618_ = lean_ctor_get(v_l_3610_, 3);
if (lean_obj_tag(v_l_3618_) == 0)
{
lean_object* v_r_3619_; 
lean_inc_ref(v_l_3618_);
lean_dec(v_h__3_3615_);
lean_dec(v_h__2_3614_);
v_r_3619_ = lean_ctor_get(v_l_3610_, 4);
if (lean_obj_tag(v_r_3619_) == 0)
{
lean_object* v_size_3620_; lean_object* v_k_3621_; lean_object* v_v_3622_; lean_object* v_size_3623_; lean_object* v_k_3624_; lean_object* v_v_3625_; lean_object* v_l_3626_; lean_object* v_r_3627_; lean_object* v_size_3628_; lean_object* v_k_3629_; lean_object* v_v_3630_; lean_object* v_l_3631_; lean_object* v_r_3632_; lean_object* v___x_3633_; 
lean_inc_ref(v_r_3619_);
lean_dec(v_h__4_3616_);
v_size_3620_ = lean_ctor_get(v_l_3610_, 0);
lean_inc(v_size_3620_);
v_k_3621_ = lean_ctor_get(v_l_3610_, 1);
lean_inc(v_k_3621_);
v_v_3622_ = lean_ctor_get(v_l_3610_, 2);
lean_inc(v_v_3622_);
lean_dec_ref(v_l_3610_);
v_size_3623_ = lean_ctor_get(v_l_3618_, 0);
lean_inc(v_size_3623_);
v_k_3624_ = lean_ctor_get(v_l_3618_, 1);
lean_inc(v_k_3624_);
v_v_3625_ = lean_ctor_get(v_l_3618_, 2);
lean_inc(v_v_3625_);
v_l_3626_ = lean_ctor_get(v_l_3618_, 3);
lean_inc(v_l_3626_);
v_r_3627_ = lean_ctor_get(v_l_3618_, 4);
lean_inc(v_r_3627_);
lean_dec_ref(v_l_3618_);
v_size_3628_ = lean_ctor_get(v_r_3619_, 0);
lean_inc(v_size_3628_);
v_k_3629_ = lean_ctor_get(v_r_3619_, 1);
lean_inc(v_k_3629_);
v_v_3630_ = lean_ctor_get(v_r_3619_, 2);
lean_inc(v_v_3630_);
v_l_3631_ = lean_ctor_get(v_r_3619_, 3);
lean_inc(v_l_3631_);
v_r_3632_ = lean_ctor_get(v_r_3619_, 4);
lean_inc(v_r_3632_);
lean_dec_ref(v_r_3619_);
v___x_3633_ = lean_apply_15(v_h__5_3617_, v_size_3620_, v_k_3621_, v_v_3622_, v_size_3623_, v_k_3624_, v_v_3625_, v_l_3626_, v_r_3627_, v_size_3628_, v_k_3629_, v_v_3630_, v_l_3631_, v_r_3632_, lean_box(0), lean_box(0));
return v___x_3633_;
}
else
{
lean_object* v_size_3634_; lean_object* v_k_3635_; lean_object* v_v_3636_; lean_object* v_size_3637_; lean_object* v_k_3638_; lean_object* v_v_3639_; lean_object* v_l_3640_; lean_object* v_r_3641_; lean_object* v___x_3642_; 
lean_dec(v_h__5_3617_);
v_size_3634_ = lean_ctor_get(v_l_3610_, 0);
lean_inc(v_size_3634_);
v_k_3635_ = lean_ctor_get(v_l_3610_, 1);
lean_inc(v_k_3635_);
v_v_3636_ = lean_ctor_get(v_l_3610_, 2);
lean_inc(v_v_3636_);
lean_dec_ref(v_l_3610_);
v_size_3637_ = lean_ctor_get(v_l_3618_, 0);
lean_inc(v_size_3637_);
v_k_3638_ = lean_ctor_get(v_l_3618_, 1);
lean_inc(v_k_3638_);
v_v_3639_ = lean_ctor_get(v_l_3618_, 2);
lean_inc(v_v_3639_);
v_l_3640_ = lean_ctor_get(v_l_3618_, 3);
lean_inc(v_l_3640_);
v_r_3641_ = lean_ctor_get(v_l_3618_, 4);
lean_inc(v_r_3641_);
lean_dec_ref(v_l_3618_);
v___x_3642_ = lean_apply_10(v_h__4_3616_, v_size_3634_, v_k_3635_, v_v_3636_, v_size_3637_, v_k_3638_, v_v_3639_, v_l_3640_, v_r_3641_, lean_box(0), lean_box(0));
return v___x_3642_;
}
}
else
{
lean_object* v_r_3643_; 
lean_dec(v_h__5_3617_);
lean_dec(v_h__4_3616_);
v_r_3643_ = lean_ctor_get(v_l_3610_, 4);
if (lean_obj_tag(v_r_3643_) == 0)
{
lean_object* v_size_3644_; lean_object* v_k_3645_; lean_object* v_v_3646_; lean_object* v_size_3647_; lean_object* v_k_3648_; lean_object* v_v_3649_; lean_object* v_l_3650_; lean_object* v_r_3651_; lean_object* v___x_3652_; 
lean_inc_ref(v_r_3643_);
lean_dec(v_h__2_3614_);
v_size_3644_ = lean_ctor_get(v_l_3610_, 0);
lean_inc(v_size_3644_);
v_k_3645_ = lean_ctor_get(v_l_3610_, 1);
lean_inc(v_k_3645_);
v_v_3646_ = lean_ctor_get(v_l_3610_, 2);
lean_inc(v_v_3646_);
lean_dec_ref(v_l_3610_);
v_size_3647_ = lean_ctor_get(v_r_3643_, 0);
lean_inc(v_size_3647_);
v_k_3648_ = lean_ctor_get(v_r_3643_, 1);
lean_inc(v_k_3648_);
v_v_3649_ = lean_ctor_get(v_r_3643_, 2);
lean_inc(v_v_3649_);
v_l_3650_ = lean_ctor_get(v_r_3643_, 3);
lean_inc(v_l_3650_);
v_r_3651_ = lean_ctor_get(v_r_3643_, 4);
lean_inc(v_r_3651_);
lean_dec_ref(v_r_3643_);
v___x_3652_ = lean_apply_10(v_h__3_3615_, v_size_3644_, v_k_3645_, v_v_3646_, v_size_3647_, v_k_3648_, v_v_3649_, v_l_3650_, v_r_3651_, lean_box(0), lean_box(0));
return v___x_3652_;
}
else
{
lean_object* v_size_3653_; lean_object* v_k_3654_; lean_object* v_v_3655_; lean_object* v___x_3656_; 
lean_dec(v_h__3_3615_);
v_size_3653_ = lean_ctor_get(v_l_3610_, 0);
lean_inc(v_size_3653_);
v_k_3654_ = lean_ctor_get(v_l_3610_, 1);
lean_inc(v_k_3654_);
v_v_3655_ = lean_ctor_get(v_l_3610_, 2);
lean_inc(v_v_3655_);
lean_dec_ref(v_l_3610_);
v___x_3656_ = lean_apply_5(v_h__2_3614_, v_size_3653_, v_k_3654_, v_v_3655_, lean_box(0), lean_box(0));
return v___x_3656_;
}
}
}
else
{
lean_object* v___x_3657_; 
lean_dec(v_h__5_3617_);
lean_dec(v_h__4_3616_);
lean_dec(v_h__3_3615_);
lean_dec(v_h__2_3614_);
v___x_3657_ = lean_apply_2(v_h__1_3613_, lean_box(0), lean_box(0));
return v___x_3657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___redArg(lean_object* v_l_3658_, lean_object* v_h__1_3659_, lean_object* v_h__2_3660_){
_start:
{
if (lean_obj_tag(v_l_3658_) == 0)
{
lean_object* v_size_3661_; lean_object* v_k_3662_; lean_object* v_v_3663_; lean_object* v_l_3664_; lean_object* v_r_3665_; lean_object* v___x_3666_; 
lean_dec(v_h__1_3659_);
v_size_3661_ = lean_ctor_get(v_l_3658_, 0);
lean_inc(v_size_3661_);
v_k_3662_ = lean_ctor_get(v_l_3658_, 1);
lean_inc(v_k_3662_);
v_v_3663_ = lean_ctor_get(v_l_3658_, 2);
lean_inc(v_v_3663_);
v_l_3664_ = lean_ctor_get(v_l_3658_, 3);
lean_inc(v_l_3664_);
v_r_3665_ = lean_ctor_get(v_l_3658_, 4);
lean_inc(v_r_3665_);
lean_dec_ref(v_l_3658_);
v___x_3666_ = lean_apply_7(v_h__2_3660_, v_size_3661_, v_k_3662_, v_v_3663_, v_l_3664_, v_r_3665_, lean_box(0), lean_box(0));
return v___x_3666_;
}
else
{
lean_object* v___x_3667_; 
lean_dec(v_h__2_3660_);
v___x_3667_ = lean_apply_2(v_h__1_3659_, lean_box(0), lean_box(0));
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter(lean_object* v_00_u03b1_3668_, lean_object* v_00_u03b2_3669_, lean_object* v_rs_3670_, lean_object* v_k_3671_, lean_object* v_v_3672_, lean_object* v_l_3673_, lean_object* v_r_3674_, lean_object* v_motive_3675_, lean_object* v_l_3676_, lean_object* v_hlb_3677_, lean_object* v_hlr_3678_, lean_object* v_h__1_3679_, lean_object* v_h__2_3680_){
_start:
{
if (lean_obj_tag(v_l_3676_) == 0)
{
lean_object* v_size_3681_; lean_object* v_k_3682_; lean_object* v_v_3683_; lean_object* v_l_3684_; lean_object* v_r_3685_; lean_object* v___x_3686_; 
lean_dec(v_h__1_3679_);
v_size_3681_ = lean_ctor_get(v_l_3676_, 0);
lean_inc(v_size_3681_);
v_k_3682_ = lean_ctor_get(v_l_3676_, 1);
lean_inc(v_k_3682_);
v_v_3683_ = lean_ctor_get(v_l_3676_, 2);
lean_inc(v_v_3683_);
v_l_3684_ = lean_ctor_get(v_l_3676_, 3);
lean_inc(v_l_3684_);
v_r_3685_ = lean_ctor_get(v_l_3676_, 4);
lean_inc(v_r_3685_);
lean_dec_ref(v_l_3676_);
v___x_3686_ = lean_apply_7(v_h__2_3680_, v_size_3681_, v_k_3682_, v_v_3683_, v_l_3684_, v_r_3685_, lean_box(0), lean_box(0));
return v___x_3686_;
}
else
{
lean_object* v___x_3687_; 
lean_dec(v_h__2_3680_);
v___x_3687_ = lean_apply_2(v_h__1_3679_, lean_box(0), lean_box(0));
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___boxed(lean_object* v_00_u03b1_3688_, lean_object* v_00_u03b2_3689_, lean_object* v_rs_3690_, lean_object* v_k_3691_, lean_object* v_v_3692_, lean_object* v_l_3693_, lean_object* v_r_3694_, lean_object* v_motive_3695_, lean_object* v_l_3696_, lean_object* v_hlb_3697_, lean_object* v_hlr_3698_, lean_object* v_h__1_3699_, lean_object* v_h__2_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter(v_00_u03b1_3688_, v_00_u03b2_3689_, v_rs_3690_, v_k_3691_, v_v_3692_, v_l_3693_, v_r_3694_, v_motive_3695_, v_l_3696_, v_hlb_3697_, v_hlr_3698_, v_h__1_3699_, v_h__2_3700_);
lean_dec(v_r_3694_);
lean_dec(v_l_3693_);
lean_dec(v_v_3692_);
lean_dec(v_k_3691_);
lean_dec(v_rs_3690_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___redArg(lean_object* v_ll_3702_, lean_object* v_lr_3703_, lean_object* v_h__1_3704_, lean_object* v_h__2_3705_, lean_object* v_h__3_3706_){
_start:
{
if (lean_obj_tag(v_ll_3702_) == 0)
{
lean_dec(v_h__3_3706_);
if (lean_obj_tag(v_lr_3703_) == 0)
{
lean_object* v_size_3707_; lean_object* v_k_3708_; lean_object* v_v_3709_; lean_object* v_l_3710_; lean_object* v_r_3711_; lean_object* v_size_3712_; lean_object* v_k_3713_; lean_object* v_v_3714_; lean_object* v_l_3715_; lean_object* v_r_3716_; lean_object* v___x_3717_; 
lean_dec(v_h__2_3705_);
v_size_3707_ = lean_ctor_get(v_ll_3702_, 0);
lean_inc(v_size_3707_);
v_k_3708_ = lean_ctor_get(v_ll_3702_, 1);
lean_inc(v_k_3708_);
v_v_3709_ = lean_ctor_get(v_ll_3702_, 2);
lean_inc(v_v_3709_);
v_l_3710_ = lean_ctor_get(v_ll_3702_, 3);
lean_inc(v_l_3710_);
v_r_3711_ = lean_ctor_get(v_ll_3702_, 4);
lean_inc(v_r_3711_);
lean_dec_ref(v_ll_3702_);
v_size_3712_ = lean_ctor_get(v_lr_3703_, 0);
lean_inc(v_size_3712_);
v_k_3713_ = lean_ctor_get(v_lr_3703_, 1);
lean_inc(v_k_3713_);
v_v_3714_ = lean_ctor_get(v_lr_3703_, 2);
lean_inc(v_v_3714_);
v_l_3715_ = lean_ctor_get(v_lr_3703_, 3);
lean_inc(v_l_3715_);
v_r_3716_ = lean_ctor_get(v_lr_3703_, 4);
lean_inc(v_r_3716_);
lean_dec_ref(v_lr_3703_);
v___x_3717_ = lean_apply_12(v_h__1_3704_, v_size_3707_, v_k_3708_, v_v_3709_, v_l_3710_, v_r_3711_, v_size_3712_, v_k_3713_, v_v_3714_, v_l_3715_, v_r_3716_, lean_box(0), lean_box(0));
return v___x_3717_;
}
else
{
lean_object* v_size_3718_; lean_object* v_k_3719_; lean_object* v_v_3720_; lean_object* v_l_3721_; lean_object* v_r_3722_; lean_object* v___x_3723_; 
lean_dec(v_h__1_3704_);
v_size_3718_ = lean_ctor_get(v_ll_3702_, 0);
lean_inc(v_size_3718_);
v_k_3719_ = lean_ctor_get(v_ll_3702_, 1);
lean_inc(v_k_3719_);
v_v_3720_ = lean_ctor_get(v_ll_3702_, 2);
lean_inc(v_v_3720_);
v_l_3721_ = lean_ctor_get(v_ll_3702_, 3);
lean_inc(v_l_3721_);
v_r_3722_ = lean_ctor_get(v_ll_3702_, 4);
lean_inc(v_r_3722_);
lean_dec_ref(v_ll_3702_);
v___x_3723_ = lean_apply_7(v_h__2_3705_, v_size_3718_, v_k_3719_, v_v_3720_, v_l_3721_, v_r_3722_, lean_box(0), lean_box(0));
return v___x_3723_;
}
}
else
{
lean_object* v___x_3724_; 
lean_dec(v_h__2_3705_);
lean_dec(v_h__1_3704_);
v___x_3724_ = lean_apply_3(v_h__3_3706_, v_lr_3703_, lean_box(0), lean_box(0));
return v___x_3724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter(lean_object* v_00_u03b1_3725_, lean_object* v_00_u03b2_3726_, lean_object* v_rs_3727_, lean_object* v_k_3728_, lean_object* v_v_3729_, lean_object* v_l_3730_, lean_object* v_r_3731_, lean_object* v_ls_3732_, lean_object* v_lk_3733_, lean_object* v_lv_3734_, lean_object* v_motive_3735_, lean_object* v_ll_3736_, lean_object* v_lr_3737_, lean_object* v_hlb_3738_, lean_object* v_hlr_3739_, lean_object* v_h__1_3740_, lean_object* v_h__2_3741_, lean_object* v_h__3_3742_){
_start:
{
if (lean_obj_tag(v_ll_3736_) == 0)
{
lean_dec(v_h__3_3742_);
if (lean_obj_tag(v_lr_3737_) == 0)
{
lean_object* v_size_3743_; lean_object* v_k_3744_; lean_object* v_v_3745_; lean_object* v_l_3746_; lean_object* v_r_3747_; lean_object* v_size_3748_; lean_object* v_k_3749_; lean_object* v_v_3750_; lean_object* v_l_3751_; lean_object* v_r_3752_; lean_object* v___x_3753_; 
lean_dec(v_h__2_3741_);
v_size_3743_ = lean_ctor_get(v_ll_3736_, 0);
lean_inc(v_size_3743_);
v_k_3744_ = lean_ctor_get(v_ll_3736_, 1);
lean_inc(v_k_3744_);
v_v_3745_ = lean_ctor_get(v_ll_3736_, 2);
lean_inc(v_v_3745_);
v_l_3746_ = lean_ctor_get(v_ll_3736_, 3);
lean_inc(v_l_3746_);
v_r_3747_ = lean_ctor_get(v_ll_3736_, 4);
lean_inc(v_r_3747_);
lean_dec_ref(v_ll_3736_);
v_size_3748_ = lean_ctor_get(v_lr_3737_, 0);
lean_inc(v_size_3748_);
v_k_3749_ = lean_ctor_get(v_lr_3737_, 1);
lean_inc(v_k_3749_);
v_v_3750_ = lean_ctor_get(v_lr_3737_, 2);
lean_inc(v_v_3750_);
v_l_3751_ = lean_ctor_get(v_lr_3737_, 3);
lean_inc(v_l_3751_);
v_r_3752_ = lean_ctor_get(v_lr_3737_, 4);
lean_inc(v_r_3752_);
lean_dec_ref(v_lr_3737_);
v___x_3753_ = lean_apply_12(v_h__1_3740_, v_size_3743_, v_k_3744_, v_v_3745_, v_l_3746_, v_r_3747_, v_size_3748_, v_k_3749_, v_v_3750_, v_l_3751_, v_r_3752_, lean_box(0), lean_box(0));
return v___x_3753_;
}
else
{
lean_object* v_size_3754_; lean_object* v_k_3755_; lean_object* v_v_3756_; lean_object* v_l_3757_; lean_object* v_r_3758_; lean_object* v___x_3759_; 
lean_dec(v_h__1_3740_);
v_size_3754_ = lean_ctor_get(v_ll_3736_, 0);
lean_inc(v_size_3754_);
v_k_3755_ = lean_ctor_get(v_ll_3736_, 1);
lean_inc(v_k_3755_);
v_v_3756_ = lean_ctor_get(v_ll_3736_, 2);
lean_inc(v_v_3756_);
v_l_3757_ = lean_ctor_get(v_ll_3736_, 3);
lean_inc(v_l_3757_);
v_r_3758_ = lean_ctor_get(v_ll_3736_, 4);
lean_inc(v_r_3758_);
lean_dec_ref(v_ll_3736_);
v___x_3759_ = lean_apply_7(v_h__2_3741_, v_size_3754_, v_k_3755_, v_v_3756_, v_l_3757_, v_r_3758_, lean_box(0), lean_box(0));
return v___x_3759_;
}
}
else
{
lean_object* v___x_3760_; 
lean_dec(v_h__2_3741_);
lean_dec(v_h__1_3740_);
v___x_3760_ = lean_apply_3(v_h__3_3742_, v_lr_3737_, lean_box(0), lean_box(0));
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___boxed(lean_object** _args){
lean_object* v_00_u03b1_3761_ = _args[0];
lean_object* v_00_u03b2_3762_ = _args[1];
lean_object* v_rs_3763_ = _args[2];
lean_object* v_k_3764_ = _args[3];
lean_object* v_v_3765_ = _args[4];
lean_object* v_l_3766_ = _args[5];
lean_object* v_r_3767_ = _args[6];
lean_object* v_ls_3768_ = _args[7];
lean_object* v_lk_3769_ = _args[8];
lean_object* v_lv_3770_ = _args[9];
lean_object* v_motive_3771_ = _args[10];
lean_object* v_ll_3772_ = _args[11];
lean_object* v_lr_3773_ = _args[12];
lean_object* v_hlb_3774_ = _args[13];
lean_object* v_hlr_3775_ = _args[14];
lean_object* v_h__1_3776_ = _args[15];
lean_object* v_h__2_3777_ = _args[16];
lean_object* v_h__3_3778_ = _args[17];
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter(v_00_u03b1_3761_, v_00_u03b2_3762_, v_rs_3763_, v_k_3764_, v_v_3765_, v_l_3766_, v_r_3767_, v_ls_3768_, v_lk_3769_, v_lv_3770_, v_motive_3771_, v_ll_3772_, v_lr_3773_, v_hlb_3774_, v_hlr_3775_, v_h__1_3776_, v_h__2_3777_, v_h__3_3778_);
lean_dec(v_lv_3770_);
lean_dec(v_lk_3769_);
lean_dec(v_ls_3768_);
lean_dec(v_r_3767_);
lean_dec(v_l_3766_);
lean_dec(v_v_3765_);
lean_dec(v_k_3764_);
lean_dec(v_rs_3763_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter___redArg(lean_object* v_l_3780_, lean_object* v_h__1_3781_, lean_object* v_h__2_3782_, lean_object* v_h__3_3783_, lean_object* v_h__4_3784_, lean_object* v_h__5_3785_){
_start:
{
if (lean_obj_tag(v_l_3780_) == 0)
{
lean_object* v_l_3786_; 
lean_dec(v_h__1_3781_);
v_l_3786_ = lean_ctor_get(v_l_3780_, 3);
if (lean_obj_tag(v_l_3786_) == 0)
{
lean_object* v_r_3787_; 
lean_inc_ref(v_l_3786_);
lean_dec(v_h__3_3783_);
lean_dec(v_h__2_3782_);
v_r_3787_ = lean_ctor_get(v_l_3780_, 4);
if (lean_obj_tag(v_r_3787_) == 0)
{
lean_object* v_size_3788_; lean_object* v_k_3789_; lean_object* v_v_3790_; lean_object* v_size_3791_; lean_object* v_k_3792_; lean_object* v_v_3793_; lean_object* v_l_3794_; lean_object* v_r_3795_; lean_object* v_size_3796_; lean_object* v_k_3797_; lean_object* v_v_3798_; lean_object* v_l_3799_; lean_object* v_r_3800_; lean_object* v___x_3801_; 
lean_inc_ref(v_r_3787_);
lean_dec(v_h__4_3784_);
v_size_3788_ = lean_ctor_get(v_l_3780_, 0);
lean_inc(v_size_3788_);
v_k_3789_ = lean_ctor_get(v_l_3780_, 1);
lean_inc(v_k_3789_);
v_v_3790_ = lean_ctor_get(v_l_3780_, 2);
lean_inc(v_v_3790_);
lean_dec_ref(v_l_3780_);
v_size_3791_ = lean_ctor_get(v_l_3786_, 0);
lean_inc(v_size_3791_);
v_k_3792_ = lean_ctor_get(v_l_3786_, 1);
lean_inc(v_k_3792_);
v_v_3793_ = lean_ctor_get(v_l_3786_, 2);
lean_inc(v_v_3793_);
v_l_3794_ = lean_ctor_get(v_l_3786_, 3);
lean_inc(v_l_3794_);
v_r_3795_ = lean_ctor_get(v_l_3786_, 4);
lean_inc(v_r_3795_);
lean_dec_ref(v_l_3786_);
v_size_3796_ = lean_ctor_get(v_r_3787_, 0);
lean_inc(v_size_3796_);
v_k_3797_ = lean_ctor_get(v_r_3787_, 1);
lean_inc(v_k_3797_);
v_v_3798_ = lean_ctor_get(v_r_3787_, 2);
lean_inc(v_v_3798_);
v_l_3799_ = lean_ctor_get(v_r_3787_, 3);
lean_inc(v_l_3799_);
v_r_3800_ = lean_ctor_get(v_r_3787_, 4);
lean_inc(v_r_3800_);
lean_dec_ref(v_r_3787_);
v___x_3801_ = lean_apply_13(v_h__5_3785_, v_size_3788_, v_k_3789_, v_v_3790_, v_size_3791_, v_k_3792_, v_v_3793_, v_l_3794_, v_r_3795_, v_size_3796_, v_k_3797_, v_v_3798_, v_l_3799_, v_r_3800_);
return v___x_3801_;
}
else
{
lean_object* v_size_3802_; lean_object* v_k_3803_; lean_object* v_v_3804_; lean_object* v_size_3805_; lean_object* v_k_3806_; lean_object* v_v_3807_; lean_object* v_l_3808_; lean_object* v_r_3809_; lean_object* v___x_3810_; 
lean_dec(v_h__5_3785_);
v_size_3802_ = lean_ctor_get(v_l_3780_, 0);
lean_inc(v_size_3802_);
v_k_3803_ = lean_ctor_get(v_l_3780_, 1);
lean_inc(v_k_3803_);
v_v_3804_ = lean_ctor_get(v_l_3780_, 2);
lean_inc(v_v_3804_);
lean_dec_ref(v_l_3780_);
v_size_3805_ = lean_ctor_get(v_l_3786_, 0);
lean_inc(v_size_3805_);
v_k_3806_ = lean_ctor_get(v_l_3786_, 1);
lean_inc(v_k_3806_);
v_v_3807_ = lean_ctor_get(v_l_3786_, 2);
lean_inc(v_v_3807_);
v_l_3808_ = lean_ctor_get(v_l_3786_, 3);
lean_inc(v_l_3808_);
v_r_3809_ = lean_ctor_get(v_l_3786_, 4);
lean_inc(v_r_3809_);
lean_dec_ref(v_l_3786_);
v___x_3810_ = lean_apply_8(v_h__4_3784_, v_size_3802_, v_k_3803_, v_v_3804_, v_size_3805_, v_k_3806_, v_v_3807_, v_l_3808_, v_r_3809_);
return v___x_3810_;
}
}
else
{
lean_object* v_r_3811_; 
lean_dec(v_h__5_3785_);
lean_dec(v_h__4_3784_);
v_r_3811_ = lean_ctor_get(v_l_3780_, 4);
if (lean_obj_tag(v_r_3811_) == 0)
{
lean_object* v_size_3812_; lean_object* v_k_3813_; lean_object* v_v_3814_; lean_object* v_size_3815_; lean_object* v_k_3816_; lean_object* v_v_3817_; lean_object* v_l_3818_; lean_object* v_r_3819_; lean_object* v___x_3820_; 
lean_inc_ref(v_r_3811_);
lean_dec(v_h__2_3782_);
v_size_3812_ = lean_ctor_get(v_l_3780_, 0);
lean_inc(v_size_3812_);
v_k_3813_ = lean_ctor_get(v_l_3780_, 1);
lean_inc(v_k_3813_);
v_v_3814_ = lean_ctor_get(v_l_3780_, 2);
lean_inc(v_v_3814_);
lean_dec_ref(v_l_3780_);
v_size_3815_ = lean_ctor_get(v_r_3811_, 0);
lean_inc(v_size_3815_);
v_k_3816_ = lean_ctor_get(v_r_3811_, 1);
lean_inc(v_k_3816_);
v_v_3817_ = lean_ctor_get(v_r_3811_, 2);
lean_inc(v_v_3817_);
v_l_3818_ = lean_ctor_get(v_r_3811_, 3);
lean_inc(v_l_3818_);
v_r_3819_ = lean_ctor_get(v_r_3811_, 4);
lean_inc(v_r_3819_);
lean_dec_ref(v_r_3811_);
v___x_3820_ = lean_apply_8(v_h__3_3783_, v_size_3812_, v_k_3813_, v_v_3814_, v_size_3815_, v_k_3816_, v_v_3817_, v_l_3818_, v_r_3819_);
return v___x_3820_;
}
else
{
lean_object* v_size_3821_; lean_object* v_k_3822_; lean_object* v_v_3823_; lean_object* v___x_3824_; 
lean_dec(v_h__3_3783_);
v_size_3821_ = lean_ctor_get(v_l_3780_, 0);
lean_inc(v_size_3821_);
v_k_3822_ = lean_ctor_get(v_l_3780_, 1);
lean_inc(v_k_3822_);
v_v_3823_ = lean_ctor_get(v_l_3780_, 2);
lean_inc(v_v_3823_);
lean_dec_ref(v_l_3780_);
v___x_3824_ = lean_apply_3(v_h__2_3782_, v_size_3821_, v_k_3822_, v_v_3823_);
return v___x_3824_;
}
}
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec(v_h__5_3785_);
lean_dec(v_h__4_3784_);
lean_dec(v_h__3_3783_);
lean_dec(v_h__2_3782_);
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_apply_1(v_h__1_3781_, v___x_3825_);
return v___x_3826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter(lean_object* v_00_u03b1_3827_, lean_object* v_00_u03b2_3828_, lean_object* v_motive_3829_, lean_object* v_l_3830_, lean_object* v_h__1_3831_, lean_object* v_h__2_3832_, lean_object* v_h__3_3833_, lean_object* v_h__4_3834_, lean_object* v_h__5_3835_){
_start:
{
if (lean_obj_tag(v_l_3830_) == 0)
{
lean_object* v_l_3836_; 
lean_dec(v_h__1_3831_);
v_l_3836_ = lean_ctor_get(v_l_3830_, 3);
if (lean_obj_tag(v_l_3836_) == 0)
{
lean_object* v_r_3837_; 
lean_inc_ref(v_l_3836_);
lean_dec(v_h__3_3833_);
lean_dec(v_h__2_3832_);
v_r_3837_ = lean_ctor_get(v_l_3830_, 4);
if (lean_obj_tag(v_r_3837_) == 0)
{
lean_object* v_size_3838_; lean_object* v_k_3839_; lean_object* v_v_3840_; lean_object* v_size_3841_; lean_object* v_k_3842_; lean_object* v_v_3843_; lean_object* v_l_3844_; lean_object* v_r_3845_; lean_object* v_size_3846_; lean_object* v_k_3847_; lean_object* v_v_3848_; lean_object* v_l_3849_; lean_object* v_r_3850_; lean_object* v___x_3851_; 
lean_inc_ref(v_r_3837_);
lean_dec(v_h__4_3834_);
v_size_3838_ = lean_ctor_get(v_l_3830_, 0);
lean_inc(v_size_3838_);
v_k_3839_ = lean_ctor_get(v_l_3830_, 1);
lean_inc(v_k_3839_);
v_v_3840_ = lean_ctor_get(v_l_3830_, 2);
lean_inc(v_v_3840_);
lean_dec_ref(v_l_3830_);
v_size_3841_ = lean_ctor_get(v_l_3836_, 0);
lean_inc(v_size_3841_);
v_k_3842_ = lean_ctor_get(v_l_3836_, 1);
lean_inc(v_k_3842_);
v_v_3843_ = lean_ctor_get(v_l_3836_, 2);
lean_inc(v_v_3843_);
v_l_3844_ = lean_ctor_get(v_l_3836_, 3);
lean_inc(v_l_3844_);
v_r_3845_ = lean_ctor_get(v_l_3836_, 4);
lean_inc(v_r_3845_);
lean_dec_ref(v_l_3836_);
v_size_3846_ = lean_ctor_get(v_r_3837_, 0);
lean_inc(v_size_3846_);
v_k_3847_ = lean_ctor_get(v_r_3837_, 1);
lean_inc(v_k_3847_);
v_v_3848_ = lean_ctor_get(v_r_3837_, 2);
lean_inc(v_v_3848_);
v_l_3849_ = lean_ctor_get(v_r_3837_, 3);
lean_inc(v_l_3849_);
v_r_3850_ = lean_ctor_get(v_r_3837_, 4);
lean_inc(v_r_3850_);
lean_dec_ref(v_r_3837_);
v___x_3851_ = lean_apply_13(v_h__5_3835_, v_size_3838_, v_k_3839_, v_v_3840_, v_size_3841_, v_k_3842_, v_v_3843_, v_l_3844_, v_r_3845_, v_size_3846_, v_k_3847_, v_v_3848_, v_l_3849_, v_r_3850_);
return v___x_3851_;
}
else
{
lean_object* v_size_3852_; lean_object* v_k_3853_; lean_object* v_v_3854_; lean_object* v_size_3855_; lean_object* v_k_3856_; lean_object* v_v_3857_; lean_object* v_l_3858_; lean_object* v_r_3859_; lean_object* v___x_3860_; 
lean_dec(v_h__5_3835_);
v_size_3852_ = lean_ctor_get(v_l_3830_, 0);
lean_inc(v_size_3852_);
v_k_3853_ = lean_ctor_get(v_l_3830_, 1);
lean_inc(v_k_3853_);
v_v_3854_ = lean_ctor_get(v_l_3830_, 2);
lean_inc(v_v_3854_);
lean_dec_ref(v_l_3830_);
v_size_3855_ = lean_ctor_get(v_l_3836_, 0);
lean_inc(v_size_3855_);
v_k_3856_ = lean_ctor_get(v_l_3836_, 1);
lean_inc(v_k_3856_);
v_v_3857_ = lean_ctor_get(v_l_3836_, 2);
lean_inc(v_v_3857_);
v_l_3858_ = lean_ctor_get(v_l_3836_, 3);
lean_inc(v_l_3858_);
v_r_3859_ = lean_ctor_get(v_l_3836_, 4);
lean_inc(v_r_3859_);
lean_dec_ref(v_l_3836_);
v___x_3860_ = lean_apply_8(v_h__4_3834_, v_size_3852_, v_k_3853_, v_v_3854_, v_size_3855_, v_k_3856_, v_v_3857_, v_l_3858_, v_r_3859_);
return v___x_3860_;
}
}
else
{
lean_object* v_r_3861_; 
lean_dec(v_h__5_3835_);
lean_dec(v_h__4_3834_);
v_r_3861_ = lean_ctor_get(v_l_3830_, 4);
if (lean_obj_tag(v_r_3861_) == 0)
{
lean_object* v_size_3862_; lean_object* v_k_3863_; lean_object* v_v_3864_; lean_object* v_size_3865_; lean_object* v_k_3866_; lean_object* v_v_3867_; lean_object* v_l_3868_; lean_object* v_r_3869_; lean_object* v___x_3870_; 
lean_inc_ref(v_r_3861_);
lean_dec(v_h__2_3832_);
v_size_3862_ = lean_ctor_get(v_l_3830_, 0);
lean_inc(v_size_3862_);
v_k_3863_ = lean_ctor_get(v_l_3830_, 1);
lean_inc(v_k_3863_);
v_v_3864_ = lean_ctor_get(v_l_3830_, 2);
lean_inc(v_v_3864_);
lean_dec_ref(v_l_3830_);
v_size_3865_ = lean_ctor_get(v_r_3861_, 0);
lean_inc(v_size_3865_);
v_k_3866_ = lean_ctor_get(v_r_3861_, 1);
lean_inc(v_k_3866_);
v_v_3867_ = lean_ctor_get(v_r_3861_, 2);
lean_inc(v_v_3867_);
v_l_3868_ = lean_ctor_get(v_r_3861_, 3);
lean_inc(v_l_3868_);
v_r_3869_ = lean_ctor_get(v_r_3861_, 4);
lean_inc(v_r_3869_);
lean_dec_ref(v_r_3861_);
v___x_3870_ = lean_apply_8(v_h__3_3833_, v_size_3862_, v_k_3863_, v_v_3864_, v_size_3865_, v_k_3866_, v_v_3867_, v_l_3868_, v_r_3869_);
return v___x_3870_;
}
else
{
lean_object* v_size_3871_; lean_object* v_k_3872_; lean_object* v_v_3873_; lean_object* v___x_3874_; 
lean_dec(v_h__3_3833_);
v_size_3871_ = lean_ctor_get(v_l_3830_, 0);
lean_inc(v_size_3871_);
v_k_3872_ = lean_ctor_get(v_l_3830_, 1);
lean_inc(v_k_3872_);
v_v_3873_ = lean_ctor_get(v_l_3830_, 2);
lean_inc(v_v_3873_);
lean_dec_ref(v_l_3830_);
v___x_3874_ = lean_apply_3(v_h__2_3832_, v_size_3871_, v_k_3872_, v_v_3873_);
return v___x_3874_;
}
}
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_dec(v_h__5_3835_);
lean_dec(v_h__4_3834_);
lean_dec(v_h__3_3833_);
lean_dec(v_h__2_3832_);
v___x_3875_ = lean_box(0);
v___x_3876_ = lean_apply_1(v_h__1_3831_, v___x_3875_);
return v___x_3876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___redArg(lean_object* v_ll_3877_, lean_object* v_lr_3878_, lean_object* v_h__1_3879_, lean_object* v_h__2_3880_, lean_object* v_h__3_3881_){
_start:
{
if (lean_obj_tag(v_ll_3877_) == 0)
{
lean_dec(v_h__3_3881_);
if (lean_obj_tag(v_lr_3878_) == 0)
{
lean_object* v_size_3882_; lean_object* v_k_3883_; lean_object* v_v_3884_; lean_object* v_l_3885_; lean_object* v_r_3886_; lean_object* v_size_3887_; lean_object* v_k_3888_; lean_object* v_v_3889_; lean_object* v_l_3890_; lean_object* v_r_3891_; lean_object* v___x_3892_; 
lean_dec(v_h__2_3880_);
v_size_3882_ = lean_ctor_get(v_ll_3877_, 0);
lean_inc(v_size_3882_);
v_k_3883_ = lean_ctor_get(v_ll_3877_, 1);
lean_inc(v_k_3883_);
v_v_3884_ = lean_ctor_get(v_ll_3877_, 2);
lean_inc(v_v_3884_);
v_l_3885_ = lean_ctor_get(v_ll_3877_, 3);
lean_inc(v_l_3885_);
v_r_3886_ = lean_ctor_get(v_ll_3877_, 4);
lean_inc(v_r_3886_);
lean_dec_ref(v_ll_3877_);
v_size_3887_ = lean_ctor_get(v_lr_3878_, 0);
lean_inc(v_size_3887_);
v_k_3888_ = lean_ctor_get(v_lr_3878_, 1);
lean_inc(v_k_3888_);
v_v_3889_ = lean_ctor_get(v_lr_3878_, 2);
lean_inc(v_v_3889_);
v_l_3890_ = lean_ctor_get(v_lr_3878_, 3);
lean_inc(v_l_3890_);
v_r_3891_ = lean_ctor_get(v_lr_3878_, 4);
lean_inc(v_r_3891_);
lean_dec_ref(v_lr_3878_);
v___x_3892_ = lean_apply_12(v_h__1_3879_, v_size_3882_, v_k_3883_, v_v_3884_, v_l_3885_, v_r_3886_, v_size_3887_, v_k_3888_, v_v_3889_, v_l_3890_, v_r_3891_, lean_box(0), lean_box(0));
return v___x_3892_;
}
else
{
lean_object* v_size_3893_; lean_object* v_k_3894_; lean_object* v_v_3895_; lean_object* v_l_3896_; lean_object* v_r_3897_; lean_object* v___x_3898_; 
lean_dec(v_h__1_3879_);
v_size_3893_ = lean_ctor_get(v_ll_3877_, 0);
lean_inc(v_size_3893_);
v_k_3894_ = lean_ctor_get(v_ll_3877_, 1);
lean_inc(v_k_3894_);
v_v_3895_ = lean_ctor_get(v_ll_3877_, 2);
lean_inc(v_v_3895_);
v_l_3896_ = lean_ctor_get(v_ll_3877_, 3);
lean_inc(v_l_3896_);
v_r_3897_ = lean_ctor_get(v_ll_3877_, 4);
lean_inc(v_r_3897_);
lean_dec_ref(v_ll_3877_);
v___x_3898_ = lean_apply_7(v_h__2_3880_, v_size_3893_, v_k_3894_, v_v_3895_, v_l_3896_, v_r_3897_, lean_box(0), lean_box(0));
return v___x_3898_;
}
}
else
{
lean_object* v___x_3899_; 
lean_dec(v_h__2_3880_);
lean_dec(v_h__1_3879_);
v___x_3899_ = lean_apply_3(v_h__3_3881_, v_lr_3878_, lean_box(0), lean_box(0));
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter(lean_object* v_00_u03b1_3900_, lean_object* v_00_u03b2_3901_, lean_object* v_rs_3902_, lean_object* v_k_3903_, lean_object* v_v_3904_, lean_object* v_l_3905_, lean_object* v_r_3906_, lean_object* v_ls_3907_, lean_object* v_lk_3908_, lean_object* v_lv_3909_, lean_object* v_motive_3910_, lean_object* v_ll_3911_, lean_object* v_lr_3912_, lean_object* v_hlb_3913_, lean_object* v_hlr_3914_, lean_object* v_h__1_3915_, lean_object* v_h__2_3916_, lean_object* v_h__3_3917_){
_start:
{
if (lean_obj_tag(v_ll_3911_) == 0)
{
lean_dec(v_h__3_3917_);
if (lean_obj_tag(v_lr_3912_) == 0)
{
lean_object* v_size_3918_; lean_object* v_k_3919_; lean_object* v_v_3920_; lean_object* v_l_3921_; lean_object* v_r_3922_; lean_object* v_size_3923_; lean_object* v_k_3924_; lean_object* v_v_3925_; lean_object* v_l_3926_; lean_object* v_r_3927_; lean_object* v___x_3928_; 
lean_dec(v_h__2_3916_);
v_size_3918_ = lean_ctor_get(v_ll_3911_, 0);
lean_inc(v_size_3918_);
v_k_3919_ = lean_ctor_get(v_ll_3911_, 1);
lean_inc(v_k_3919_);
v_v_3920_ = lean_ctor_get(v_ll_3911_, 2);
lean_inc(v_v_3920_);
v_l_3921_ = lean_ctor_get(v_ll_3911_, 3);
lean_inc(v_l_3921_);
v_r_3922_ = lean_ctor_get(v_ll_3911_, 4);
lean_inc(v_r_3922_);
lean_dec_ref(v_ll_3911_);
v_size_3923_ = lean_ctor_get(v_lr_3912_, 0);
lean_inc(v_size_3923_);
v_k_3924_ = lean_ctor_get(v_lr_3912_, 1);
lean_inc(v_k_3924_);
v_v_3925_ = lean_ctor_get(v_lr_3912_, 2);
lean_inc(v_v_3925_);
v_l_3926_ = lean_ctor_get(v_lr_3912_, 3);
lean_inc(v_l_3926_);
v_r_3927_ = lean_ctor_get(v_lr_3912_, 4);
lean_inc(v_r_3927_);
lean_dec_ref(v_lr_3912_);
v___x_3928_ = lean_apply_12(v_h__1_3915_, v_size_3918_, v_k_3919_, v_v_3920_, v_l_3921_, v_r_3922_, v_size_3923_, v_k_3924_, v_v_3925_, v_l_3926_, v_r_3927_, lean_box(0), lean_box(0));
return v___x_3928_;
}
else
{
lean_object* v_size_3929_; lean_object* v_k_3930_; lean_object* v_v_3931_; lean_object* v_l_3932_; lean_object* v_r_3933_; lean_object* v___x_3934_; 
lean_dec(v_h__1_3915_);
v_size_3929_ = lean_ctor_get(v_ll_3911_, 0);
lean_inc(v_size_3929_);
v_k_3930_ = lean_ctor_get(v_ll_3911_, 1);
lean_inc(v_k_3930_);
v_v_3931_ = lean_ctor_get(v_ll_3911_, 2);
lean_inc(v_v_3931_);
v_l_3932_ = lean_ctor_get(v_ll_3911_, 3);
lean_inc(v_l_3932_);
v_r_3933_ = lean_ctor_get(v_ll_3911_, 4);
lean_inc(v_r_3933_);
lean_dec_ref(v_ll_3911_);
v___x_3934_ = lean_apply_7(v_h__2_3916_, v_size_3929_, v_k_3930_, v_v_3931_, v_l_3932_, v_r_3933_, lean_box(0), lean_box(0));
return v___x_3934_;
}
}
else
{
lean_object* v___x_3935_; 
lean_dec(v_h__2_3916_);
lean_dec(v_h__1_3915_);
v___x_3935_ = lean_apply_3(v_h__3_3917_, v_lr_3912_, lean_box(0), lean_box(0));
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___boxed(lean_object** _args){
lean_object* v_00_u03b1_3936_ = _args[0];
lean_object* v_00_u03b2_3937_ = _args[1];
lean_object* v_rs_3938_ = _args[2];
lean_object* v_k_3939_ = _args[3];
lean_object* v_v_3940_ = _args[4];
lean_object* v_l_3941_ = _args[5];
lean_object* v_r_3942_ = _args[6];
lean_object* v_ls_3943_ = _args[7];
lean_object* v_lk_3944_ = _args[8];
lean_object* v_lv_3945_ = _args[9];
lean_object* v_motive_3946_ = _args[10];
lean_object* v_ll_3947_ = _args[11];
lean_object* v_lr_3948_ = _args[12];
lean_object* v_hlb_3949_ = _args[13];
lean_object* v_hlr_3950_ = _args[14];
lean_object* v_h__1_3951_ = _args[15];
lean_object* v_h__2_3952_ = _args[16];
lean_object* v_h__3_3953_ = _args[17];
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter(v_00_u03b1_3936_, v_00_u03b2_3937_, v_rs_3938_, v_k_3939_, v_v_3940_, v_l_3941_, v_r_3942_, v_ls_3943_, v_lk_3944_, v_lv_3945_, v_motive_3946_, v_ll_3947_, v_lr_3948_, v_hlb_3949_, v_hlr_3950_, v_h__1_3951_, v_h__2_3952_, v_h__3_3953_);
lean_dec(v_lv_3945_);
lean_dec(v_lk_3944_);
lean_dec(v_ls_3943_);
lean_dec(v_r_3942_);
lean_dec(v_l_3941_);
lean_dec(v_v_3940_);
lean_dec(v_k_3939_);
lean_dec(v_rs_3938_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter___redArg(lean_object* v_r_3955_, lean_object* v_h__1_3956_, lean_object* v_h__2_3957_, lean_object* v_h__3_3958_, lean_object* v_h__4_3959_, lean_object* v_h__5_3960_){
_start:
{
if (lean_obj_tag(v_r_3955_) == 0)
{
lean_object* v_l_3961_; 
lean_dec(v_h__1_3956_);
v_l_3961_ = lean_ctor_get(v_r_3955_, 3);
if (lean_obj_tag(v_l_3961_) == 0)
{
lean_object* v_r_3962_; 
lean_inc_ref(v_l_3961_);
lean_dec(v_h__3_3958_);
lean_dec(v_h__2_3957_);
v_r_3962_ = lean_ctor_get(v_r_3955_, 4);
if (lean_obj_tag(v_r_3962_) == 0)
{
lean_object* v_size_3963_; lean_object* v_k_3964_; lean_object* v_v_3965_; lean_object* v_size_3966_; lean_object* v_k_3967_; lean_object* v_v_3968_; lean_object* v_l_3969_; lean_object* v_r_3970_; lean_object* v_size_3971_; lean_object* v_k_3972_; lean_object* v_v_3973_; lean_object* v_l_3974_; lean_object* v_r_3975_; lean_object* v___x_3976_; 
lean_inc_ref(v_r_3962_);
lean_dec(v_h__4_3959_);
v_size_3963_ = lean_ctor_get(v_r_3955_, 0);
lean_inc(v_size_3963_);
v_k_3964_ = lean_ctor_get(v_r_3955_, 1);
lean_inc(v_k_3964_);
v_v_3965_ = lean_ctor_get(v_r_3955_, 2);
lean_inc(v_v_3965_);
lean_dec_ref(v_r_3955_);
v_size_3966_ = lean_ctor_get(v_l_3961_, 0);
lean_inc(v_size_3966_);
v_k_3967_ = lean_ctor_get(v_l_3961_, 1);
lean_inc(v_k_3967_);
v_v_3968_ = lean_ctor_get(v_l_3961_, 2);
lean_inc(v_v_3968_);
v_l_3969_ = lean_ctor_get(v_l_3961_, 3);
lean_inc(v_l_3969_);
v_r_3970_ = lean_ctor_get(v_l_3961_, 4);
lean_inc(v_r_3970_);
lean_dec_ref(v_l_3961_);
v_size_3971_ = lean_ctor_get(v_r_3962_, 0);
lean_inc(v_size_3971_);
v_k_3972_ = lean_ctor_get(v_r_3962_, 1);
lean_inc(v_k_3972_);
v_v_3973_ = lean_ctor_get(v_r_3962_, 2);
lean_inc(v_v_3973_);
v_l_3974_ = lean_ctor_get(v_r_3962_, 3);
lean_inc(v_l_3974_);
v_r_3975_ = lean_ctor_get(v_r_3962_, 4);
lean_inc(v_r_3975_);
lean_dec_ref(v_r_3962_);
v___x_3976_ = lean_apply_15(v_h__5_3960_, v_size_3963_, v_k_3964_, v_v_3965_, v_size_3966_, v_k_3967_, v_v_3968_, v_l_3969_, v_r_3970_, v_size_3971_, v_k_3972_, v_v_3973_, v_l_3974_, v_r_3975_, lean_box(0), lean_box(0));
return v___x_3976_;
}
else
{
lean_object* v_size_3977_; lean_object* v_k_3978_; lean_object* v_v_3979_; lean_object* v_size_3980_; lean_object* v_k_3981_; lean_object* v_v_3982_; lean_object* v_l_3983_; lean_object* v_r_3984_; lean_object* v___x_3985_; 
lean_dec(v_h__5_3960_);
v_size_3977_ = lean_ctor_get(v_r_3955_, 0);
lean_inc(v_size_3977_);
v_k_3978_ = lean_ctor_get(v_r_3955_, 1);
lean_inc(v_k_3978_);
v_v_3979_ = lean_ctor_get(v_r_3955_, 2);
lean_inc(v_v_3979_);
lean_dec_ref(v_r_3955_);
v_size_3980_ = lean_ctor_get(v_l_3961_, 0);
lean_inc(v_size_3980_);
v_k_3981_ = lean_ctor_get(v_l_3961_, 1);
lean_inc(v_k_3981_);
v_v_3982_ = lean_ctor_get(v_l_3961_, 2);
lean_inc(v_v_3982_);
v_l_3983_ = lean_ctor_get(v_l_3961_, 3);
lean_inc(v_l_3983_);
v_r_3984_ = lean_ctor_get(v_l_3961_, 4);
lean_inc(v_r_3984_);
lean_dec_ref(v_l_3961_);
v___x_3985_ = lean_apply_10(v_h__4_3959_, v_size_3977_, v_k_3978_, v_v_3979_, v_size_3980_, v_k_3981_, v_v_3982_, v_l_3983_, v_r_3984_, lean_box(0), lean_box(0));
return v___x_3985_;
}
}
else
{
lean_object* v_r_3986_; 
lean_dec(v_h__5_3960_);
lean_dec(v_h__4_3959_);
v_r_3986_ = lean_ctor_get(v_r_3955_, 4);
if (lean_obj_tag(v_r_3986_) == 0)
{
lean_object* v_size_3987_; lean_object* v_k_3988_; lean_object* v_v_3989_; lean_object* v_size_3990_; lean_object* v_k_3991_; lean_object* v_v_3992_; lean_object* v_l_3993_; lean_object* v_r_3994_; lean_object* v___x_3995_; 
lean_inc_ref(v_r_3986_);
lean_dec(v_h__2_3957_);
v_size_3987_ = lean_ctor_get(v_r_3955_, 0);
lean_inc(v_size_3987_);
v_k_3988_ = lean_ctor_get(v_r_3955_, 1);
lean_inc(v_k_3988_);
v_v_3989_ = lean_ctor_get(v_r_3955_, 2);
lean_inc(v_v_3989_);
lean_dec_ref(v_r_3955_);
v_size_3990_ = lean_ctor_get(v_r_3986_, 0);
lean_inc(v_size_3990_);
v_k_3991_ = lean_ctor_get(v_r_3986_, 1);
lean_inc(v_k_3991_);
v_v_3992_ = lean_ctor_get(v_r_3986_, 2);
lean_inc(v_v_3992_);
v_l_3993_ = lean_ctor_get(v_r_3986_, 3);
lean_inc(v_l_3993_);
v_r_3994_ = lean_ctor_get(v_r_3986_, 4);
lean_inc(v_r_3994_);
lean_dec_ref(v_r_3986_);
v___x_3995_ = lean_apply_10(v_h__3_3958_, v_size_3987_, v_k_3988_, v_v_3989_, v_size_3990_, v_k_3991_, v_v_3992_, v_l_3993_, v_r_3994_, lean_box(0), lean_box(0));
return v___x_3995_;
}
else
{
lean_object* v_size_3996_; lean_object* v_k_3997_; lean_object* v_v_3998_; lean_object* v___x_3999_; 
lean_dec(v_h__3_3958_);
v_size_3996_ = lean_ctor_get(v_r_3955_, 0);
lean_inc(v_size_3996_);
v_k_3997_ = lean_ctor_get(v_r_3955_, 1);
lean_inc(v_k_3997_);
v_v_3998_ = lean_ctor_get(v_r_3955_, 2);
lean_inc(v_v_3998_);
lean_dec_ref(v_r_3955_);
v___x_3999_ = lean_apply_5(v_h__2_3957_, v_size_3996_, v_k_3997_, v_v_3998_, lean_box(0), lean_box(0));
return v___x_3999_;
}
}
}
else
{
lean_object* v___x_4000_; 
lean_dec(v_h__5_3960_);
lean_dec(v_h__4_3959_);
lean_dec(v_h__3_3958_);
lean_dec(v_h__2_3957_);
v___x_4000_ = lean_apply_2(v_h__1_3956_, lean_box(0), lean_box(0));
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter(lean_object* v_00_u03b1_4001_, lean_object* v_00_u03b2_4002_, lean_object* v_motive_4003_, lean_object* v_r_4004_, lean_object* v_hrb_4005_, lean_object* v_hlr_4006_, lean_object* v_h__1_4007_, lean_object* v_h__2_4008_, lean_object* v_h__3_4009_, lean_object* v_h__4_4010_, lean_object* v_h__5_4011_){
_start:
{
if (lean_obj_tag(v_r_4004_) == 0)
{
lean_object* v_l_4012_; 
lean_dec(v_h__1_4007_);
v_l_4012_ = lean_ctor_get(v_r_4004_, 3);
if (lean_obj_tag(v_l_4012_) == 0)
{
lean_object* v_r_4013_; 
lean_inc_ref(v_l_4012_);
lean_dec(v_h__3_4009_);
lean_dec(v_h__2_4008_);
v_r_4013_ = lean_ctor_get(v_r_4004_, 4);
if (lean_obj_tag(v_r_4013_) == 0)
{
lean_object* v_size_4014_; lean_object* v_k_4015_; lean_object* v_v_4016_; lean_object* v_size_4017_; lean_object* v_k_4018_; lean_object* v_v_4019_; lean_object* v_l_4020_; lean_object* v_r_4021_; lean_object* v_size_4022_; lean_object* v_k_4023_; lean_object* v_v_4024_; lean_object* v_l_4025_; lean_object* v_r_4026_; lean_object* v___x_4027_; 
lean_inc_ref(v_r_4013_);
lean_dec(v_h__4_4010_);
v_size_4014_ = lean_ctor_get(v_r_4004_, 0);
lean_inc(v_size_4014_);
v_k_4015_ = lean_ctor_get(v_r_4004_, 1);
lean_inc(v_k_4015_);
v_v_4016_ = lean_ctor_get(v_r_4004_, 2);
lean_inc(v_v_4016_);
lean_dec_ref(v_r_4004_);
v_size_4017_ = lean_ctor_get(v_l_4012_, 0);
lean_inc(v_size_4017_);
v_k_4018_ = lean_ctor_get(v_l_4012_, 1);
lean_inc(v_k_4018_);
v_v_4019_ = lean_ctor_get(v_l_4012_, 2);
lean_inc(v_v_4019_);
v_l_4020_ = lean_ctor_get(v_l_4012_, 3);
lean_inc(v_l_4020_);
v_r_4021_ = lean_ctor_get(v_l_4012_, 4);
lean_inc(v_r_4021_);
lean_dec_ref(v_l_4012_);
v_size_4022_ = lean_ctor_get(v_r_4013_, 0);
lean_inc(v_size_4022_);
v_k_4023_ = lean_ctor_get(v_r_4013_, 1);
lean_inc(v_k_4023_);
v_v_4024_ = lean_ctor_get(v_r_4013_, 2);
lean_inc(v_v_4024_);
v_l_4025_ = lean_ctor_get(v_r_4013_, 3);
lean_inc(v_l_4025_);
v_r_4026_ = lean_ctor_get(v_r_4013_, 4);
lean_inc(v_r_4026_);
lean_dec_ref(v_r_4013_);
v___x_4027_ = lean_apply_15(v_h__5_4011_, v_size_4014_, v_k_4015_, v_v_4016_, v_size_4017_, v_k_4018_, v_v_4019_, v_l_4020_, v_r_4021_, v_size_4022_, v_k_4023_, v_v_4024_, v_l_4025_, v_r_4026_, lean_box(0), lean_box(0));
return v___x_4027_;
}
else
{
lean_object* v_size_4028_; lean_object* v_k_4029_; lean_object* v_v_4030_; lean_object* v_size_4031_; lean_object* v_k_4032_; lean_object* v_v_4033_; lean_object* v_l_4034_; lean_object* v_r_4035_; lean_object* v___x_4036_; 
lean_dec(v_h__5_4011_);
v_size_4028_ = lean_ctor_get(v_r_4004_, 0);
lean_inc(v_size_4028_);
v_k_4029_ = lean_ctor_get(v_r_4004_, 1);
lean_inc(v_k_4029_);
v_v_4030_ = lean_ctor_get(v_r_4004_, 2);
lean_inc(v_v_4030_);
lean_dec_ref(v_r_4004_);
v_size_4031_ = lean_ctor_get(v_l_4012_, 0);
lean_inc(v_size_4031_);
v_k_4032_ = lean_ctor_get(v_l_4012_, 1);
lean_inc(v_k_4032_);
v_v_4033_ = lean_ctor_get(v_l_4012_, 2);
lean_inc(v_v_4033_);
v_l_4034_ = lean_ctor_get(v_l_4012_, 3);
lean_inc(v_l_4034_);
v_r_4035_ = lean_ctor_get(v_l_4012_, 4);
lean_inc(v_r_4035_);
lean_dec_ref(v_l_4012_);
v___x_4036_ = lean_apply_10(v_h__4_4010_, v_size_4028_, v_k_4029_, v_v_4030_, v_size_4031_, v_k_4032_, v_v_4033_, v_l_4034_, v_r_4035_, lean_box(0), lean_box(0));
return v___x_4036_;
}
}
else
{
lean_object* v_r_4037_; 
lean_dec(v_h__5_4011_);
lean_dec(v_h__4_4010_);
v_r_4037_ = lean_ctor_get(v_r_4004_, 4);
if (lean_obj_tag(v_r_4037_) == 0)
{
lean_object* v_size_4038_; lean_object* v_k_4039_; lean_object* v_v_4040_; lean_object* v_size_4041_; lean_object* v_k_4042_; lean_object* v_v_4043_; lean_object* v_l_4044_; lean_object* v_r_4045_; lean_object* v___x_4046_; 
lean_inc_ref(v_r_4037_);
lean_dec(v_h__2_4008_);
v_size_4038_ = lean_ctor_get(v_r_4004_, 0);
lean_inc(v_size_4038_);
v_k_4039_ = lean_ctor_get(v_r_4004_, 1);
lean_inc(v_k_4039_);
v_v_4040_ = lean_ctor_get(v_r_4004_, 2);
lean_inc(v_v_4040_);
lean_dec_ref(v_r_4004_);
v_size_4041_ = lean_ctor_get(v_r_4037_, 0);
lean_inc(v_size_4041_);
v_k_4042_ = lean_ctor_get(v_r_4037_, 1);
lean_inc(v_k_4042_);
v_v_4043_ = lean_ctor_get(v_r_4037_, 2);
lean_inc(v_v_4043_);
v_l_4044_ = lean_ctor_get(v_r_4037_, 3);
lean_inc(v_l_4044_);
v_r_4045_ = lean_ctor_get(v_r_4037_, 4);
lean_inc(v_r_4045_);
lean_dec_ref(v_r_4037_);
v___x_4046_ = lean_apply_10(v_h__3_4009_, v_size_4038_, v_k_4039_, v_v_4040_, v_size_4041_, v_k_4042_, v_v_4043_, v_l_4044_, v_r_4045_, lean_box(0), lean_box(0));
return v___x_4046_;
}
else
{
lean_object* v_size_4047_; lean_object* v_k_4048_; lean_object* v_v_4049_; lean_object* v___x_4050_; 
lean_dec(v_h__3_4009_);
v_size_4047_ = lean_ctor_get(v_r_4004_, 0);
lean_inc(v_size_4047_);
v_k_4048_ = lean_ctor_get(v_r_4004_, 1);
lean_inc(v_k_4048_);
v_v_4049_ = lean_ctor_get(v_r_4004_, 2);
lean_inc(v_v_4049_);
lean_dec_ref(v_r_4004_);
v___x_4050_ = lean_apply_5(v_h__2_4008_, v_size_4047_, v_k_4048_, v_v_4049_, lean_box(0), lean_box(0));
return v___x_4050_;
}
}
}
else
{
lean_object* v___x_4051_; 
lean_dec(v_h__5_4011_);
lean_dec(v_h__4_4010_);
lean_dec(v_h__3_4009_);
lean_dec(v_h__2_4008_);
v___x_4051_ = lean_apply_2(v_h__1_4007_, lean_box(0), lean_box(0));
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___redArg(lean_object* v_r_4052_, lean_object* v_h__1_4053_, lean_object* v_h__2_4054_){
_start:
{
if (lean_obj_tag(v_r_4052_) == 0)
{
lean_object* v_size_4055_; lean_object* v_k_4056_; lean_object* v_v_4057_; lean_object* v_l_4058_; lean_object* v_r_4059_; lean_object* v___x_4060_; 
lean_dec(v_h__1_4053_);
v_size_4055_ = lean_ctor_get(v_r_4052_, 0);
lean_inc(v_size_4055_);
v_k_4056_ = lean_ctor_get(v_r_4052_, 1);
lean_inc(v_k_4056_);
v_v_4057_ = lean_ctor_get(v_r_4052_, 2);
lean_inc(v_v_4057_);
v_l_4058_ = lean_ctor_get(v_r_4052_, 3);
lean_inc(v_l_4058_);
v_r_4059_ = lean_ctor_get(v_r_4052_, 4);
lean_inc(v_r_4059_);
lean_dec_ref(v_r_4052_);
v___x_4060_ = lean_apply_7(v_h__2_4054_, v_size_4055_, v_k_4056_, v_v_4057_, v_l_4058_, v_r_4059_, lean_box(0), lean_box(0));
return v___x_4060_;
}
else
{
lean_object* v___x_4061_; 
lean_dec(v_h__2_4054_);
v___x_4061_ = lean_apply_2(v_h__1_4053_, lean_box(0), lean_box(0));
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter(lean_object* v_00_u03b1_4062_, lean_object* v_00_u03b2_4063_, lean_object* v_l_4064_, lean_object* v_motive_4065_, lean_object* v_r_4066_, lean_object* v_hrb_4067_, lean_object* v_hlr_4068_, lean_object* v_h__1_4069_, lean_object* v_h__2_4070_){
_start:
{
if (lean_obj_tag(v_r_4066_) == 0)
{
lean_object* v_size_4071_; lean_object* v_k_4072_; lean_object* v_v_4073_; lean_object* v_l_4074_; lean_object* v_r_4075_; lean_object* v___x_4076_; 
lean_dec(v_h__1_4069_);
v_size_4071_ = lean_ctor_get(v_r_4066_, 0);
lean_inc(v_size_4071_);
v_k_4072_ = lean_ctor_get(v_r_4066_, 1);
lean_inc(v_k_4072_);
v_v_4073_ = lean_ctor_get(v_r_4066_, 2);
lean_inc(v_v_4073_);
v_l_4074_ = lean_ctor_get(v_r_4066_, 3);
lean_inc(v_l_4074_);
v_r_4075_ = lean_ctor_get(v_r_4066_, 4);
lean_inc(v_r_4075_);
lean_dec_ref(v_r_4066_);
v___x_4076_ = lean_apply_7(v_h__2_4070_, v_size_4071_, v_k_4072_, v_v_4073_, v_l_4074_, v_r_4075_, lean_box(0), lean_box(0));
return v___x_4076_;
}
else
{
lean_object* v___x_4077_; 
lean_dec(v_h__2_4070_);
v___x_4077_ = lean_apply_2(v_h__1_4069_, lean_box(0), lean_box(0));
return v___x_4077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___boxed(lean_object* v_00_u03b1_4078_, lean_object* v_00_u03b2_4079_, lean_object* v_l_4080_, lean_object* v_motive_4081_, lean_object* v_r_4082_, lean_object* v_hrb_4083_, lean_object* v_hlr_4084_, lean_object* v_h__1_4085_, lean_object* v_h__2_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter(v_00_u03b1_4078_, v_00_u03b2_4079_, v_l_4080_, v_motive_4081_, v_r_4082_, v_hrb_4083_, v_hlr_4084_, v_h__1_4085_, v_h__2_4086_);
lean_dec(v_l_4080_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter___redArg(lean_object* v_r_4088_, lean_object* v_h__1_4089_, lean_object* v_h__2_4090_, lean_object* v_h__3_4091_, lean_object* v_h__4_4092_, lean_object* v_h__5_4093_){
_start:
{
if (lean_obj_tag(v_r_4088_) == 0)
{
lean_object* v_l_4094_; 
lean_dec(v_h__1_4089_);
v_l_4094_ = lean_ctor_get(v_r_4088_, 3);
if (lean_obj_tag(v_l_4094_) == 0)
{
lean_object* v_r_4095_; 
lean_inc_ref(v_l_4094_);
lean_dec(v_h__3_4091_);
lean_dec(v_h__2_4090_);
v_r_4095_ = lean_ctor_get(v_r_4088_, 4);
if (lean_obj_tag(v_r_4095_) == 0)
{
lean_object* v_size_4096_; lean_object* v_k_4097_; lean_object* v_v_4098_; lean_object* v_size_4099_; lean_object* v_k_4100_; lean_object* v_v_4101_; lean_object* v_l_4102_; lean_object* v_r_4103_; lean_object* v_size_4104_; lean_object* v_k_4105_; lean_object* v_v_4106_; lean_object* v_l_4107_; lean_object* v_r_4108_; lean_object* v___x_4109_; 
lean_inc_ref(v_r_4095_);
lean_dec(v_h__4_4092_);
v_size_4096_ = lean_ctor_get(v_r_4088_, 0);
lean_inc(v_size_4096_);
v_k_4097_ = lean_ctor_get(v_r_4088_, 1);
lean_inc(v_k_4097_);
v_v_4098_ = lean_ctor_get(v_r_4088_, 2);
lean_inc(v_v_4098_);
lean_dec_ref(v_r_4088_);
v_size_4099_ = lean_ctor_get(v_l_4094_, 0);
lean_inc(v_size_4099_);
v_k_4100_ = lean_ctor_get(v_l_4094_, 1);
lean_inc(v_k_4100_);
v_v_4101_ = lean_ctor_get(v_l_4094_, 2);
lean_inc(v_v_4101_);
v_l_4102_ = lean_ctor_get(v_l_4094_, 3);
lean_inc(v_l_4102_);
v_r_4103_ = lean_ctor_get(v_l_4094_, 4);
lean_inc(v_r_4103_);
lean_dec_ref(v_l_4094_);
v_size_4104_ = lean_ctor_get(v_r_4095_, 0);
lean_inc(v_size_4104_);
v_k_4105_ = lean_ctor_get(v_r_4095_, 1);
lean_inc(v_k_4105_);
v_v_4106_ = lean_ctor_get(v_r_4095_, 2);
lean_inc(v_v_4106_);
v_l_4107_ = lean_ctor_get(v_r_4095_, 3);
lean_inc(v_l_4107_);
v_r_4108_ = lean_ctor_get(v_r_4095_, 4);
lean_inc(v_r_4108_);
lean_dec_ref(v_r_4095_);
v___x_4109_ = lean_apply_15(v_h__5_4093_, v_size_4096_, v_k_4097_, v_v_4098_, v_size_4099_, v_k_4100_, v_v_4101_, v_l_4102_, v_r_4103_, v_size_4104_, v_k_4105_, v_v_4106_, v_l_4107_, v_r_4108_, lean_box(0), lean_box(0));
return v___x_4109_;
}
else
{
lean_object* v_size_4110_; lean_object* v_k_4111_; lean_object* v_v_4112_; lean_object* v_size_4113_; lean_object* v_k_4114_; lean_object* v_v_4115_; lean_object* v_l_4116_; lean_object* v_r_4117_; lean_object* v___x_4118_; 
lean_dec(v_h__5_4093_);
v_size_4110_ = lean_ctor_get(v_r_4088_, 0);
lean_inc(v_size_4110_);
v_k_4111_ = lean_ctor_get(v_r_4088_, 1);
lean_inc(v_k_4111_);
v_v_4112_ = lean_ctor_get(v_r_4088_, 2);
lean_inc(v_v_4112_);
lean_dec_ref(v_r_4088_);
v_size_4113_ = lean_ctor_get(v_l_4094_, 0);
lean_inc(v_size_4113_);
v_k_4114_ = lean_ctor_get(v_l_4094_, 1);
lean_inc(v_k_4114_);
v_v_4115_ = lean_ctor_get(v_l_4094_, 2);
lean_inc(v_v_4115_);
v_l_4116_ = lean_ctor_get(v_l_4094_, 3);
lean_inc(v_l_4116_);
v_r_4117_ = lean_ctor_get(v_l_4094_, 4);
lean_inc(v_r_4117_);
lean_dec_ref(v_l_4094_);
v___x_4118_ = lean_apply_10(v_h__4_4092_, v_size_4110_, v_k_4111_, v_v_4112_, v_size_4113_, v_k_4114_, v_v_4115_, v_l_4116_, v_r_4117_, lean_box(0), lean_box(0));
return v___x_4118_;
}
}
else
{
lean_object* v_r_4119_; 
lean_dec(v_h__5_4093_);
lean_dec(v_h__4_4092_);
v_r_4119_ = lean_ctor_get(v_r_4088_, 4);
if (lean_obj_tag(v_r_4119_) == 0)
{
lean_object* v_size_4120_; lean_object* v_k_4121_; lean_object* v_v_4122_; lean_object* v_size_4123_; lean_object* v_k_4124_; lean_object* v_v_4125_; lean_object* v_l_4126_; lean_object* v_r_4127_; lean_object* v___x_4128_; 
lean_inc_ref(v_r_4119_);
lean_dec(v_h__2_4090_);
v_size_4120_ = lean_ctor_get(v_r_4088_, 0);
lean_inc(v_size_4120_);
v_k_4121_ = lean_ctor_get(v_r_4088_, 1);
lean_inc(v_k_4121_);
v_v_4122_ = lean_ctor_get(v_r_4088_, 2);
lean_inc(v_v_4122_);
lean_dec_ref(v_r_4088_);
v_size_4123_ = lean_ctor_get(v_r_4119_, 0);
lean_inc(v_size_4123_);
v_k_4124_ = lean_ctor_get(v_r_4119_, 1);
lean_inc(v_k_4124_);
v_v_4125_ = lean_ctor_get(v_r_4119_, 2);
lean_inc(v_v_4125_);
v_l_4126_ = lean_ctor_get(v_r_4119_, 3);
lean_inc(v_l_4126_);
v_r_4127_ = lean_ctor_get(v_r_4119_, 4);
lean_inc(v_r_4127_);
lean_dec_ref(v_r_4119_);
v___x_4128_ = lean_apply_10(v_h__3_4091_, v_size_4120_, v_k_4121_, v_v_4122_, v_size_4123_, v_k_4124_, v_v_4125_, v_l_4126_, v_r_4127_, lean_box(0), lean_box(0));
return v___x_4128_;
}
else
{
lean_object* v_size_4129_; lean_object* v_k_4130_; lean_object* v_v_4131_; lean_object* v___x_4132_; 
lean_dec(v_h__3_4091_);
v_size_4129_ = lean_ctor_get(v_r_4088_, 0);
lean_inc(v_size_4129_);
v_k_4130_ = lean_ctor_get(v_r_4088_, 1);
lean_inc(v_k_4130_);
v_v_4131_ = lean_ctor_get(v_r_4088_, 2);
lean_inc(v_v_4131_);
lean_dec_ref(v_r_4088_);
v___x_4132_ = lean_apply_5(v_h__2_4090_, v_size_4129_, v_k_4130_, v_v_4131_, lean_box(0), lean_box(0));
return v___x_4132_;
}
}
}
else
{
lean_object* v___x_4133_; 
lean_dec(v_h__5_4093_);
lean_dec(v_h__4_4092_);
lean_dec(v_h__3_4091_);
lean_dec(v_h__2_4090_);
v___x_4133_ = lean_apply_2(v_h__1_4089_, lean_box(0), lean_box(0));
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter(lean_object* v_00_u03b1_4134_, lean_object* v_00_u03b2_4135_, lean_object* v_motive_4136_, lean_object* v_r_4137_, lean_object* v_hrb_4138_, lean_object* v_hlr_4139_, lean_object* v_h__1_4140_, lean_object* v_h__2_4141_, lean_object* v_h__3_4142_, lean_object* v_h__4_4143_, lean_object* v_h__5_4144_){
_start:
{
if (lean_obj_tag(v_r_4137_) == 0)
{
lean_object* v_l_4145_; 
lean_dec(v_h__1_4140_);
v_l_4145_ = lean_ctor_get(v_r_4137_, 3);
if (lean_obj_tag(v_l_4145_) == 0)
{
lean_object* v_r_4146_; 
lean_inc_ref(v_l_4145_);
lean_dec(v_h__3_4142_);
lean_dec(v_h__2_4141_);
v_r_4146_ = lean_ctor_get(v_r_4137_, 4);
if (lean_obj_tag(v_r_4146_) == 0)
{
lean_object* v_size_4147_; lean_object* v_k_4148_; lean_object* v_v_4149_; lean_object* v_size_4150_; lean_object* v_k_4151_; lean_object* v_v_4152_; lean_object* v_l_4153_; lean_object* v_r_4154_; lean_object* v_size_4155_; lean_object* v_k_4156_; lean_object* v_v_4157_; lean_object* v_l_4158_; lean_object* v_r_4159_; lean_object* v___x_4160_; 
lean_inc_ref(v_r_4146_);
lean_dec(v_h__4_4143_);
v_size_4147_ = lean_ctor_get(v_r_4137_, 0);
lean_inc(v_size_4147_);
v_k_4148_ = lean_ctor_get(v_r_4137_, 1);
lean_inc(v_k_4148_);
v_v_4149_ = lean_ctor_get(v_r_4137_, 2);
lean_inc(v_v_4149_);
lean_dec_ref(v_r_4137_);
v_size_4150_ = lean_ctor_get(v_l_4145_, 0);
lean_inc(v_size_4150_);
v_k_4151_ = lean_ctor_get(v_l_4145_, 1);
lean_inc(v_k_4151_);
v_v_4152_ = lean_ctor_get(v_l_4145_, 2);
lean_inc(v_v_4152_);
v_l_4153_ = lean_ctor_get(v_l_4145_, 3);
lean_inc(v_l_4153_);
v_r_4154_ = lean_ctor_get(v_l_4145_, 4);
lean_inc(v_r_4154_);
lean_dec_ref(v_l_4145_);
v_size_4155_ = lean_ctor_get(v_r_4146_, 0);
lean_inc(v_size_4155_);
v_k_4156_ = lean_ctor_get(v_r_4146_, 1);
lean_inc(v_k_4156_);
v_v_4157_ = lean_ctor_get(v_r_4146_, 2);
lean_inc(v_v_4157_);
v_l_4158_ = lean_ctor_get(v_r_4146_, 3);
lean_inc(v_l_4158_);
v_r_4159_ = lean_ctor_get(v_r_4146_, 4);
lean_inc(v_r_4159_);
lean_dec_ref(v_r_4146_);
v___x_4160_ = lean_apply_15(v_h__5_4144_, v_size_4147_, v_k_4148_, v_v_4149_, v_size_4150_, v_k_4151_, v_v_4152_, v_l_4153_, v_r_4154_, v_size_4155_, v_k_4156_, v_v_4157_, v_l_4158_, v_r_4159_, lean_box(0), lean_box(0));
return v___x_4160_;
}
else
{
lean_object* v_size_4161_; lean_object* v_k_4162_; lean_object* v_v_4163_; lean_object* v_size_4164_; lean_object* v_k_4165_; lean_object* v_v_4166_; lean_object* v_l_4167_; lean_object* v_r_4168_; lean_object* v___x_4169_; 
lean_dec(v_h__5_4144_);
v_size_4161_ = lean_ctor_get(v_r_4137_, 0);
lean_inc(v_size_4161_);
v_k_4162_ = lean_ctor_get(v_r_4137_, 1);
lean_inc(v_k_4162_);
v_v_4163_ = lean_ctor_get(v_r_4137_, 2);
lean_inc(v_v_4163_);
lean_dec_ref(v_r_4137_);
v_size_4164_ = lean_ctor_get(v_l_4145_, 0);
lean_inc(v_size_4164_);
v_k_4165_ = lean_ctor_get(v_l_4145_, 1);
lean_inc(v_k_4165_);
v_v_4166_ = lean_ctor_get(v_l_4145_, 2);
lean_inc(v_v_4166_);
v_l_4167_ = lean_ctor_get(v_l_4145_, 3);
lean_inc(v_l_4167_);
v_r_4168_ = lean_ctor_get(v_l_4145_, 4);
lean_inc(v_r_4168_);
lean_dec_ref(v_l_4145_);
v___x_4169_ = lean_apply_10(v_h__4_4143_, v_size_4161_, v_k_4162_, v_v_4163_, v_size_4164_, v_k_4165_, v_v_4166_, v_l_4167_, v_r_4168_, lean_box(0), lean_box(0));
return v___x_4169_;
}
}
else
{
lean_object* v_r_4170_; 
lean_dec(v_h__5_4144_);
lean_dec(v_h__4_4143_);
v_r_4170_ = lean_ctor_get(v_r_4137_, 4);
if (lean_obj_tag(v_r_4170_) == 0)
{
lean_object* v_size_4171_; lean_object* v_k_4172_; lean_object* v_v_4173_; lean_object* v_size_4174_; lean_object* v_k_4175_; lean_object* v_v_4176_; lean_object* v_l_4177_; lean_object* v_r_4178_; lean_object* v___x_4179_; 
lean_inc_ref(v_r_4170_);
lean_dec(v_h__2_4141_);
v_size_4171_ = lean_ctor_get(v_r_4137_, 0);
lean_inc(v_size_4171_);
v_k_4172_ = lean_ctor_get(v_r_4137_, 1);
lean_inc(v_k_4172_);
v_v_4173_ = lean_ctor_get(v_r_4137_, 2);
lean_inc(v_v_4173_);
lean_dec_ref(v_r_4137_);
v_size_4174_ = lean_ctor_get(v_r_4170_, 0);
lean_inc(v_size_4174_);
v_k_4175_ = lean_ctor_get(v_r_4170_, 1);
lean_inc(v_k_4175_);
v_v_4176_ = lean_ctor_get(v_r_4170_, 2);
lean_inc(v_v_4176_);
v_l_4177_ = lean_ctor_get(v_r_4170_, 3);
lean_inc(v_l_4177_);
v_r_4178_ = lean_ctor_get(v_r_4170_, 4);
lean_inc(v_r_4178_);
lean_dec_ref(v_r_4170_);
v___x_4179_ = lean_apply_10(v_h__3_4142_, v_size_4171_, v_k_4172_, v_v_4173_, v_size_4174_, v_k_4175_, v_v_4176_, v_l_4177_, v_r_4178_, lean_box(0), lean_box(0));
return v___x_4179_;
}
else
{
lean_object* v_size_4180_; lean_object* v_k_4181_; lean_object* v_v_4182_; lean_object* v___x_4183_; 
lean_dec(v_h__3_4142_);
v_size_4180_ = lean_ctor_get(v_r_4137_, 0);
lean_inc(v_size_4180_);
v_k_4181_ = lean_ctor_get(v_r_4137_, 1);
lean_inc(v_k_4181_);
v_v_4182_ = lean_ctor_get(v_r_4137_, 2);
lean_inc(v_v_4182_);
lean_dec_ref(v_r_4137_);
v___x_4183_ = lean_apply_5(v_h__2_4141_, v_size_4180_, v_k_4181_, v_v_4182_, lean_box(0), lean_box(0));
return v___x_4183_;
}
}
}
else
{
lean_object* v___x_4184_; 
lean_dec(v_h__5_4144_);
lean_dec(v_h__4_4143_);
lean_dec(v_h__3_4142_);
lean_dec(v_h__2_4141_);
v___x_4184_ = lean_apply_2(v_h__1_4140_, lean_box(0), lean_box(0));
return v___x_4184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___redArg(lean_object* v_l_4185_, lean_object* v_h__1_4186_, lean_object* v_h__2_4187_){
_start:
{
if (lean_obj_tag(v_l_4185_) == 0)
{
lean_object* v_size_4188_; lean_object* v_k_4189_; lean_object* v_v_4190_; lean_object* v_l_4191_; lean_object* v_r_4192_; lean_object* v___x_4193_; 
lean_dec(v_h__1_4186_);
v_size_4188_ = lean_ctor_get(v_l_4185_, 0);
lean_inc(v_size_4188_);
v_k_4189_ = lean_ctor_get(v_l_4185_, 1);
lean_inc(v_k_4189_);
v_v_4190_ = lean_ctor_get(v_l_4185_, 2);
lean_inc(v_v_4190_);
v_l_4191_ = lean_ctor_get(v_l_4185_, 3);
lean_inc(v_l_4191_);
v_r_4192_ = lean_ctor_get(v_l_4185_, 4);
lean_inc(v_r_4192_);
lean_dec_ref(v_l_4185_);
v___x_4193_ = lean_apply_7(v_h__2_4187_, v_size_4188_, v_k_4189_, v_v_4190_, v_l_4191_, v_r_4192_, lean_box(0), lean_box(0));
return v___x_4193_;
}
else
{
lean_object* v___x_4194_; 
lean_dec(v_h__2_4187_);
v___x_4194_ = lean_apply_2(v_h__1_4186_, lean_box(0), lean_box(0));
return v___x_4194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter(lean_object* v_00_u03b1_4195_, lean_object* v_00_u03b2_4196_, lean_object* v_rs_4197_, lean_object* v_k_4198_, lean_object* v_v_4199_, lean_object* v_l_4200_, lean_object* v_r_4201_, lean_object* v_motive_4202_, lean_object* v_l_4203_, lean_object* v_hlb_4204_, lean_object* v_hlr_4205_, lean_object* v_h__1_4206_, lean_object* v_h__2_4207_){
_start:
{
if (lean_obj_tag(v_l_4203_) == 0)
{
lean_object* v_size_4208_; lean_object* v_k_4209_; lean_object* v_v_4210_; lean_object* v_l_4211_; lean_object* v_r_4212_; lean_object* v___x_4213_; 
lean_dec(v_h__1_4206_);
v_size_4208_ = lean_ctor_get(v_l_4203_, 0);
lean_inc(v_size_4208_);
v_k_4209_ = lean_ctor_get(v_l_4203_, 1);
lean_inc(v_k_4209_);
v_v_4210_ = lean_ctor_get(v_l_4203_, 2);
lean_inc(v_v_4210_);
v_l_4211_ = lean_ctor_get(v_l_4203_, 3);
lean_inc(v_l_4211_);
v_r_4212_ = lean_ctor_get(v_l_4203_, 4);
lean_inc(v_r_4212_);
lean_dec_ref(v_l_4203_);
v___x_4213_ = lean_apply_7(v_h__2_4207_, v_size_4208_, v_k_4209_, v_v_4210_, v_l_4211_, v_r_4212_, lean_box(0), lean_box(0));
return v___x_4213_;
}
else
{
lean_object* v___x_4214_; 
lean_dec(v_h__2_4207_);
v___x_4214_ = lean_apply_2(v_h__1_4206_, lean_box(0), lean_box(0));
return v___x_4214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___boxed(lean_object* v_00_u03b1_4215_, lean_object* v_00_u03b2_4216_, lean_object* v_rs_4217_, lean_object* v_k_4218_, lean_object* v_v_4219_, lean_object* v_l_4220_, lean_object* v_r_4221_, lean_object* v_motive_4222_, lean_object* v_l_4223_, lean_object* v_hlb_4224_, lean_object* v_hlr_4225_, lean_object* v_h__1_4226_, lean_object* v_h__2_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter(v_00_u03b1_4215_, v_00_u03b2_4216_, v_rs_4217_, v_k_4218_, v_v_4219_, v_l_4220_, v_r_4221_, v_motive_4222_, v_l_4223_, v_hlb_4224_, v_hlr_4225_, v_h__1_4226_, v_h__2_4227_);
lean_dec(v_r_4221_);
lean_dec(v_l_4220_);
lean_dec(v_v_4219_);
lean_dec(v_k_4218_);
lean_dec(v_rs_4217_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter___redArg(lean_object* v_r_4229_, lean_object* v_h__1_4230_, lean_object* v_h__2_4231_, lean_object* v_h__3_4232_, lean_object* v_h__4_4233_, lean_object* v_h__5_4234_){
_start:
{
if (lean_obj_tag(v_r_4229_) == 0)
{
lean_object* v_l_4235_; 
lean_dec(v_h__1_4230_);
v_l_4235_ = lean_ctor_get(v_r_4229_, 3);
if (lean_obj_tag(v_l_4235_) == 0)
{
lean_object* v_r_4236_; 
lean_inc_ref(v_l_4235_);
lean_dec(v_h__3_4232_);
lean_dec(v_h__2_4231_);
v_r_4236_ = lean_ctor_get(v_r_4229_, 4);
if (lean_obj_tag(v_r_4236_) == 0)
{
lean_object* v_size_4237_; lean_object* v_k_4238_; lean_object* v_v_4239_; lean_object* v_size_4240_; lean_object* v_k_4241_; lean_object* v_v_4242_; lean_object* v_l_4243_; lean_object* v_r_4244_; lean_object* v_size_4245_; lean_object* v_k_4246_; lean_object* v_v_4247_; lean_object* v_l_4248_; lean_object* v_r_4249_; lean_object* v___x_4250_; 
lean_inc_ref(v_r_4236_);
lean_dec(v_h__4_4233_);
v_size_4237_ = lean_ctor_get(v_r_4229_, 0);
lean_inc(v_size_4237_);
v_k_4238_ = lean_ctor_get(v_r_4229_, 1);
lean_inc(v_k_4238_);
v_v_4239_ = lean_ctor_get(v_r_4229_, 2);
lean_inc(v_v_4239_);
lean_dec_ref(v_r_4229_);
v_size_4240_ = lean_ctor_get(v_l_4235_, 0);
lean_inc(v_size_4240_);
v_k_4241_ = lean_ctor_get(v_l_4235_, 1);
lean_inc(v_k_4241_);
v_v_4242_ = lean_ctor_get(v_l_4235_, 2);
lean_inc(v_v_4242_);
v_l_4243_ = lean_ctor_get(v_l_4235_, 3);
lean_inc(v_l_4243_);
v_r_4244_ = lean_ctor_get(v_l_4235_, 4);
lean_inc(v_r_4244_);
lean_dec_ref(v_l_4235_);
v_size_4245_ = lean_ctor_get(v_r_4236_, 0);
lean_inc(v_size_4245_);
v_k_4246_ = lean_ctor_get(v_r_4236_, 1);
lean_inc(v_k_4246_);
v_v_4247_ = lean_ctor_get(v_r_4236_, 2);
lean_inc(v_v_4247_);
v_l_4248_ = lean_ctor_get(v_r_4236_, 3);
lean_inc(v_l_4248_);
v_r_4249_ = lean_ctor_get(v_r_4236_, 4);
lean_inc(v_r_4249_);
lean_dec_ref(v_r_4236_);
v___x_4250_ = lean_apply_13(v_h__5_4234_, v_size_4237_, v_k_4238_, v_v_4239_, v_size_4240_, v_k_4241_, v_v_4242_, v_l_4243_, v_r_4244_, v_size_4245_, v_k_4246_, v_v_4247_, v_l_4248_, v_r_4249_);
return v___x_4250_;
}
else
{
lean_object* v_size_4251_; lean_object* v_k_4252_; lean_object* v_v_4253_; lean_object* v_size_4254_; lean_object* v_k_4255_; lean_object* v_v_4256_; lean_object* v_l_4257_; lean_object* v_r_4258_; lean_object* v___x_4259_; 
lean_dec(v_h__5_4234_);
v_size_4251_ = lean_ctor_get(v_r_4229_, 0);
lean_inc(v_size_4251_);
v_k_4252_ = lean_ctor_get(v_r_4229_, 1);
lean_inc(v_k_4252_);
v_v_4253_ = lean_ctor_get(v_r_4229_, 2);
lean_inc(v_v_4253_);
lean_dec_ref(v_r_4229_);
v_size_4254_ = lean_ctor_get(v_l_4235_, 0);
lean_inc(v_size_4254_);
v_k_4255_ = lean_ctor_get(v_l_4235_, 1);
lean_inc(v_k_4255_);
v_v_4256_ = lean_ctor_get(v_l_4235_, 2);
lean_inc(v_v_4256_);
v_l_4257_ = lean_ctor_get(v_l_4235_, 3);
lean_inc(v_l_4257_);
v_r_4258_ = lean_ctor_get(v_l_4235_, 4);
lean_inc(v_r_4258_);
lean_dec_ref(v_l_4235_);
v___x_4259_ = lean_apply_8(v_h__4_4233_, v_size_4251_, v_k_4252_, v_v_4253_, v_size_4254_, v_k_4255_, v_v_4256_, v_l_4257_, v_r_4258_);
return v___x_4259_;
}
}
else
{
lean_object* v_r_4260_; 
lean_dec(v_h__5_4234_);
lean_dec(v_h__4_4233_);
v_r_4260_ = lean_ctor_get(v_r_4229_, 4);
if (lean_obj_tag(v_r_4260_) == 0)
{
lean_object* v_size_4261_; lean_object* v_k_4262_; lean_object* v_v_4263_; lean_object* v_size_4264_; lean_object* v_k_4265_; lean_object* v_v_4266_; lean_object* v_l_4267_; lean_object* v_r_4268_; lean_object* v___x_4269_; 
lean_inc_ref(v_r_4260_);
lean_dec(v_h__2_4231_);
v_size_4261_ = lean_ctor_get(v_r_4229_, 0);
lean_inc(v_size_4261_);
v_k_4262_ = lean_ctor_get(v_r_4229_, 1);
lean_inc(v_k_4262_);
v_v_4263_ = lean_ctor_get(v_r_4229_, 2);
lean_inc(v_v_4263_);
lean_dec_ref(v_r_4229_);
v_size_4264_ = lean_ctor_get(v_r_4260_, 0);
lean_inc(v_size_4264_);
v_k_4265_ = lean_ctor_get(v_r_4260_, 1);
lean_inc(v_k_4265_);
v_v_4266_ = lean_ctor_get(v_r_4260_, 2);
lean_inc(v_v_4266_);
v_l_4267_ = lean_ctor_get(v_r_4260_, 3);
lean_inc(v_l_4267_);
v_r_4268_ = lean_ctor_get(v_r_4260_, 4);
lean_inc(v_r_4268_);
lean_dec_ref(v_r_4260_);
v___x_4269_ = lean_apply_8(v_h__3_4232_, v_size_4261_, v_k_4262_, v_v_4263_, v_size_4264_, v_k_4265_, v_v_4266_, v_l_4267_, v_r_4268_);
return v___x_4269_;
}
else
{
lean_object* v_size_4270_; lean_object* v_k_4271_; lean_object* v_v_4272_; lean_object* v___x_4273_; 
lean_dec(v_h__3_4232_);
v_size_4270_ = lean_ctor_get(v_r_4229_, 0);
lean_inc(v_size_4270_);
v_k_4271_ = lean_ctor_get(v_r_4229_, 1);
lean_inc(v_k_4271_);
v_v_4272_ = lean_ctor_get(v_r_4229_, 2);
lean_inc(v_v_4272_);
lean_dec_ref(v_r_4229_);
v___x_4273_ = lean_apply_3(v_h__2_4231_, v_size_4270_, v_k_4271_, v_v_4272_);
return v___x_4273_;
}
}
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_dec(v_h__5_4234_);
lean_dec(v_h__4_4233_);
lean_dec(v_h__3_4232_);
lean_dec(v_h__2_4231_);
v___x_4274_ = lean_box(0);
v___x_4275_ = lean_apply_1(v_h__1_4230_, v___x_4274_);
return v___x_4275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter(lean_object* v_00_u03b1_4276_, lean_object* v_00_u03b2_4277_, lean_object* v_motive_4278_, lean_object* v_r_4279_, lean_object* v_h__1_4280_, lean_object* v_h__2_4281_, lean_object* v_h__3_4282_, lean_object* v_h__4_4283_, lean_object* v_h__5_4284_){
_start:
{
if (lean_obj_tag(v_r_4279_) == 0)
{
lean_object* v_l_4285_; 
lean_dec(v_h__1_4280_);
v_l_4285_ = lean_ctor_get(v_r_4279_, 3);
if (lean_obj_tag(v_l_4285_) == 0)
{
lean_object* v_r_4286_; 
lean_inc_ref(v_l_4285_);
lean_dec(v_h__3_4282_);
lean_dec(v_h__2_4281_);
v_r_4286_ = lean_ctor_get(v_r_4279_, 4);
if (lean_obj_tag(v_r_4286_) == 0)
{
lean_object* v_size_4287_; lean_object* v_k_4288_; lean_object* v_v_4289_; lean_object* v_size_4290_; lean_object* v_k_4291_; lean_object* v_v_4292_; lean_object* v_l_4293_; lean_object* v_r_4294_; lean_object* v_size_4295_; lean_object* v_k_4296_; lean_object* v_v_4297_; lean_object* v_l_4298_; lean_object* v_r_4299_; lean_object* v___x_4300_; 
lean_inc_ref(v_r_4286_);
lean_dec(v_h__4_4283_);
v_size_4287_ = lean_ctor_get(v_r_4279_, 0);
lean_inc(v_size_4287_);
v_k_4288_ = lean_ctor_get(v_r_4279_, 1);
lean_inc(v_k_4288_);
v_v_4289_ = lean_ctor_get(v_r_4279_, 2);
lean_inc(v_v_4289_);
lean_dec_ref(v_r_4279_);
v_size_4290_ = lean_ctor_get(v_l_4285_, 0);
lean_inc(v_size_4290_);
v_k_4291_ = lean_ctor_get(v_l_4285_, 1);
lean_inc(v_k_4291_);
v_v_4292_ = lean_ctor_get(v_l_4285_, 2);
lean_inc(v_v_4292_);
v_l_4293_ = lean_ctor_get(v_l_4285_, 3);
lean_inc(v_l_4293_);
v_r_4294_ = lean_ctor_get(v_l_4285_, 4);
lean_inc(v_r_4294_);
lean_dec_ref(v_l_4285_);
v_size_4295_ = lean_ctor_get(v_r_4286_, 0);
lean_inc(v_size_4295_);
v_k_4296_ = lean_ctor_get(v_r_4286_, 1);
lean_inc(v_k_4296_);
v_v_4297_ = lean_ctor_get(v_r_4286_, 2);
lean_inc(v_v_4297_);
v_l_4298_ = lean_ctor_get(v_r_4286_, 3);
lean_inc(v_l_4298_);
v_r_4299_ = lean_ctor_get(v_r_4286_, 4);
lean_inc(v_r_4299_);
lean_dec_ref(v_r_4286_);
v___x_4300_ = lean_apply_13(v_h__5_4284_, v_size_4287_, v_k_4288_, v_v_4289_, v_size_4290_, v_k_4291_, v_v_4292_, v_l_4293_, v_r_4294_, v_size_4295_, v_k_4296_, v_v_4297_, v_l_4298_, v_r_4299_);
return v___x_4300_;
}
else
{
lean_object* v_size_4301_; lean_object* v_k_4302_; lean_object* v_v_4303_; lean_object* v_size_4304_; lean_object* v_k_4305_; lean_object* v_v_4306_; lean_object* v_l_4307_; lean_object* v_r_4308_; lean_object* v___x_4309_; 
lean_dec(v_h__5_4284_);
v_size_4301_ = lean_ctor_get(v_r_4279_, 0);
lean_inc(v_size_4301_);
v_k_4302_ = lean_ctor_get(v_r_4279_, 1);
lean_inc(v_k_4302_);
v_v_4303_ = lean_ctor_get(v_r_4279_, 2);
lean_inc(v_v_4303_);
lean_dec_ref(v_r_4279_);
v_size_4304_ = lean_ctor_get(v_l_4285_, 0);
lean_inc(v_size_4304_);
v_k_4305_ = lean_ctor_get(v_l_4285_, 1);
lean_inc(v_k_4305_);
v_v_4306_ = lean_ctor_get(v_l_4285_, 2);
lean_inc(v_v_4306_);
v_l_4307_ = lean_ctor_get(v_l_4285_, 3);
lean_inc(v_l_4307_);
v_r_4308_ = lean_ctor_get(v_l_4285_, 4);
lean_inc(v_r_4308_);
lean_dec_ref(v_l_4285_);
v___x_4309_ = lean_apply_8(v_h__4_4283_, v_size_4301_, v_k_4302_, v_v_4303_, v_size_4304_, v_k_4305_, v_v_4306_, v_l_4307_, v_r_4308_);
return v___x_4309_;
}
}
else
{
lean_object* v_r_4310_; 
lean_dec(v_h__5_4284_);
lean_dec(v_h__4_4283_);
v_r_4310_ = lean_ctor_get(v_r_4279_, 4);
if (lean_obj_tag(v_r_4310_) == 0)
{
lean_object* v_size_4311_; lean_object* v_k_4312_; lean_object* v_v_4313_; lean_object* v_size_4314_; lean_object* v_k_4315_; lean_object* v_v_4316_; lean_object* v_l_4317_; lean_object* v_r_4318_; lean_object* v___x_4319_; 
lean_inc_ref(v_r_4310_);
lean_dec(v_h__2_4281_);
v_size_4311_ = lean_ctor_get(v_r_4279_, 0);
lean_inc(v_size_4311_);
v_k_4312_ = lean_ctor_get(v_r_4279_, 1);
lean_inc(v_k_4312_);
v_v_4313_ = lean_ctor_get(v_r_4279_, 2);
lean_inc(v_v_4313_);
lean_dec_ref(v_r_4279_);
v_size_4314_ = lean_ctor_get(v_r_4310_, 0);
lean_inc(v_size_4314_);
v_k_4315_ = lean_ctor_get(v_r_4310_, 1);
lean_inc(v_k_4315_);
v_v_4316_ = lean_ctor_get(v_r_4310_, 2);
lean_inc(v_v_4316_);
v_l_4317_ = lean_ctor_get(v_r_4310_, 3);
lean_inc(v_l_4317_);
v_r_4318_ = lean_ctor_get(v_r_4310_, 4);
lean_inc(v_r_4318_);
lean_dec_ref(v_r_4310_);
v___x_4319_ = lean_apply_8(v_h__3_4282_, v_size_4311_, v_k_4312_, v_v_4313_, v_size_4314_, v_k_4315_, v_v_4316_, v_l_4317_, v_r_4318_);
return v___x_4319_;
}
else
{
lean_object* v_size_4320_; lean_object* v_k_4321_; lean_object* v_v_4322_; lean_object* v___x_4323_; 
lean_dec(v_h__3_4282_);
v_size_4320_ = lean_ctor_get(v_r_4279_, 0);
lean_inc(v_size_4320_);
v_k_4321_ = lean_ctor_get(v_r_4279_, 1);
lean_inc(v_k_4321_);
v_v_4322_ = lean_ctor_get(v_r_4279_, 2);
lean_inc(v_v_4322_);
lean_dec_ref(v_r_4279_);
v___x_4323_ = lean_apply_3(v_h__2_4281_, v_size_4320_, v_k_4321_, v_v_4322_);
return v___x_4323_;
}
}
}
else
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
lean_dec(v_h__5_4284_);
lean_dec(v_h__4_4283_);
lean_dec(v_h__3_4282_);
lean_dec(v_h__2_4281_);
v___x_4324_ = lean_box(0);
v___x_4325_ = lean_apply_1(v_h__1_4280_, v___x_4324_);
return v___x_4325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object* v_r_4326_, lean_object* v_h__1_4327_, lean_object* v_h__2_4328_){
_start:
{
if (lean_obj_tag(v_r_4326_) == 0)
{
lean_object* v_size_4329_; lean_object* v_k_4330_; lean_object* v_v_4331_; lean_object* v_l_4332_; lean_object* v_r_4333_; lean_object* v___x_4334_; 
lean_dec(v_h__1_4327_);
v_size_4329_ = lean_ctor_get(v_r_4326_, 0);
lean_inc(v_size_4329_);
v_k_4330_ = lean_ctor_get(v_r_4326_, 1);
lean_inc(v_k_4330_);
v_v_4331_ = lean_ctor_get(v_r_4326_, 2);
lean_inc(v_v_4331_);
v_l_4332_ = lean_ctor_get(v_r_4326_, 3);
lean_inc(v_l_4332_);
v_r_4333_ = lean_ctor_get(v_r_4326_, 4);
lean_inc(v_r_4333_);
lean_dec_ref(v_r_4326_);
v___x_4334_ = lean_apply_6(v_h__2_4328_, v_size_4329_, v_k_4330_, v_v_4331_, v_l_4332_, v_r_4333_, lean_box(0));
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; 
lean_dec(v_h__2_4328_);
v___x_4335_ = lean_apply_1(v_h__1_4327_, lean_box(0));
return v___x_4335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object* v_00_u03b1_4336_, lean_object* v_00_u03b2_4337_, lean_object* v_l_4338_, lean_object* v_motive_4339_, lean_object* v_r_4340_, lean_object* v_h_4341_, lean_object* v_h__1_4342_, lean_object* v_h__2_4343_){
_start:
{
if (lean_obj_tag(v_r_4340_) == 0)
{
lean_object* v_size_4344_; lean_object* v_k_4345_; lean_object* v_v_4346_; lean_object* v_l_4347_; lean_object* v_r_4348_; lean_object* v___x_4349_; 
lean_dec(v_h__1_4342_);
v_size_4344_ = lean_ctor_get(v_r_4340_, 0);
lean_inc(v_size_4344_);
v_k_4345_ = lean_ctor_get(v_r_4340_, 1);
lean_inc(v_k_4345_);
v_v_4346_ = lean_ctor_get(v_r_4340_, 2);
lean_inc(v_v_4346_);
v_l_4347_ = lean_ctor_get(v_r_4340_, 3);
lean_inc(v_l_4347_);
v_r_4348_ = lean_ctor_get(v_r_4340_, 4);
lean_inc(v_r_4348_);
lean_dec_ref(v_r_4340_);
v___x_4349_ = lean_apply_6(v_h__2_4343_, v_size_4344_, v_k_4345_, v_v_4346_, v_l_4347_, v_r_4348_, lean_box(0));
return v___x_4349_;
}
else
{
lean_object* v___x_4350_; 
lean_dec(v_h__2_4343_);
v___x_4350_ = lean_apply_1(v_h__1_4342_, lean_box(0));
return v___x_4350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_4351_, lean_object* v_00_u03b2_4352_, lean_object* v_l_4353_, lean_object* v_motive_4354_, lean_object* v_r_4355_, lean_object* v_h_4356_, lean_object* v_h__1_4357_, lean_object* v_h__2_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_4351_, v_00_u03b2_4352_, v_l_4353_, v_motive_4354_, v_r_4355_, v_h_4356_, v_h__1_4357_, v_h__2_4358_);
lean_dec(v_l_4353_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object* v_l_4360_, lean_object* v_h__1_4361_, lean_object* v_h__2_4362_){
_start:
{
if (lean_obj_tag(v_l_4360_) == 0)
{
lean_object* v_size_4363_; lean_object* v_k_4364_; lean_object* v_v_4365_; lean_object* v_l_4366_; lean_object* v_r_4367_; lean_object* v___x_4368_; 
lean_dec(v_h__1_4361_);
v_size_4363_ = lean_ctor_get(v_l_4360_, 0);
lean_inc(v_size_4363_);
v_k_4364_ = lean_ctor_get(v_l_4360_, 1);
lean_inc(v_k_4364_);
v_v_4365_ = lean_ctor_get(v_l_4360_, 2);
lean_inc(v_v_4365_);
v_l_4366_ = lean_ctor_get(v_l_4360_, 3);
lean_inc(v_l_4366_);
v_r_4367_ = lean_ctor_get(v_l_4360_, 4);
lean_inc(v_r_4367_);
lean_dec_ref(v_l_4360_);
v___x_4368_ = lean_apply_7(v_h__2_4362_, v_size_4363_, v_k_4364_, v_v_4365_, v_l_4366_, v_r_4367_, lean_box(0), lean_box(0));
return v___x_4368_;
}
else
{
lean_object* v___x_4369_; 
lean_dec(v_h__2_4362_);
v___x_4369_ = lean_apply_2(v_h__1_4361_, lean_box(0), lean_box(0));
return v___x_4369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object* v_00_u03b1_4370_, lean_object* v_00_u03b2_4371_, lean_object* v_r_4372_, lean_object* v_motive_4373_, lean_object* v_l_4374_, lean_object* v_h_4375_, lean_object* v_h_4376_, lean_object* v_h__1_4377_, lean_object* v_h__2_4378_){
_start:
{
if (lean_obj_tag(v_l_4374_) == 0)
{
lean_object* v_size_4379_; lean_object* v_k_4380_; lean_object* v_v_4381_; lean_object* v_l_4382_; lean_object* v_r_4383_; lean_object* v___x_4384_; 
lean_dec(v_h__1_4377_);
v_size_4379_ = lean_ctor_get(v_l_4374_, 0);
lean_inc(v_size_4379_);
v_k_4380_ = lean_ctor_get(v_l_4374_, 1);
lean_inc(v_k_4380_);
v_v_4381_ = lean_ctor_get(v_l_4374_, 2);
lean_inc(v_v_4381_);
v_l_4382_ = lean_ctor_get(v_l_4374_, 3);
lean_inc(v_l_4382_);
v_r_4383_ = lean_ctor_get(v_l_4374_, 4);
lean_inc(v_r_4383_);
lean_dec_ref(v_l_4374_);
v___x_4384_ = lean_apply_7(v_h__2_4378_, v_size_4379_, v_k_4380_, v_v_4381_, v_l_4382_, v_r_4383_, lean_box(0), lean_box(0));
return v___x_4384_;
}
else
{
lean_object* v___x_4385_; 
lean_dec(v_h__2_4378_);
v___x_4385_ = lean_apply_2(v_h__1_4377_, lean_box(0), lean_box(0));
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object* v_00_u03b1_4386_, lean_object* v_00_u03b2_4387_, lean_object* v_r_4388_, lean_object* v_motive_4389_, lean_object* v_l_4390_, lean_object* v_h_4391_, lean_object* v_h_4392_, lean_object* v_h__1_4393_, lean_object* v_h__2_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_4386_, v_00_u03b2_4387_, v_r_4388_, v_motive_4389_, v_l_4390_, v_h_4391_, v_h_4392_, v_h__1_4393_, v_h__2_4394_);
lean_dec(v_r_4388_);
return v_res_4395_;
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
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Balanced(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
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
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Balanced(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Balancing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Balancing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Balancing(builtin);
}
#ifdef __cplusplus
}
#endif
