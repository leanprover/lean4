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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___boxed(lean_object*, lean_object*, lean_object*);
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
v_currMacroScope_205_ = lean_ctor_get(v_a_198_, 2);
v_ref_206_ = lean_ctor_get(v_a_198_, 5);
v___x_207_ = 0;
v___x_208_ = l_Lean_SourceInfo_fromRef(v_ref_206_, v___x_207_);
v___x_209_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__4));
v___x_210_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__5));
lean_inc_n(v___x_208_, 90);
v___x_211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_208_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7));
v___x_213_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9));
v___x_214_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11));
v___x_215_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__13));
v___x_216_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__14));
v___x_217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_208_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = l_Lean_Syntax_node1(v___x_208_, v___x_215_, v___x_217_);
v___x_219_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__15);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_208_);
lean_ctor_set(v___x_220_, 1, v___x_214_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__16));
v___x_222_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__17));
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_208_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
v___x_224_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__18));
v___x_225_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__19));
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_208_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_inc_ref_n(v___x_220_, 18);
v___x_227_ = l_Lean_Syntax_node3(v___x_208_, v___x_225_, v___x_226_, v___x_220_, v___x_220_);
v___x_228_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_227_);
v___x_229_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_228_);
v___x_230_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_229_);
lean_inc_ref(v___x_223_);
v___x_231_ = l_Lean_Syntax_node2(v___x_208_, v___x_222_, v___x_223_, v___x_230_);
v___x_232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__21));
v___x_233_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__22));
v___x_234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_208_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__24));
v___x_236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__25));
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_208_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__26));
v___x_239_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__27));
v___x_240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_208_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
v___x_241_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__29));
v___x_242_ = l_Lean_Syntax_node1(v___x_208_, v___x_241_, v___x_220_);
v___x_243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__30));
v___x_244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_208_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_244_);
v___x_246_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__31));
v___x_247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_208_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__33));
v___x_249_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__35);
v___x_250_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__36));
lean_inc_n(v_currMacroScope_205_, 2);
lean_inc_n(v_quotContext_204_, 2);
v___x_251_ = l_Lean_addMacroScope(v_quotContext_204_, v___x_250_, v_currMacroScope_205_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_253_, 0, v___x_208_);
lean_ctor_set(v___x_253_, 1, v___x_249_);
lean_ctor_set(v___x_253_, 2, v___x_251_);
lean_ctor_set(v___x_253_, 3, v___x_252_);
v___x_254_ = l_Lean_Syntax_node3(v___x_208_, v___x_248_, v___x_220_, v___x_220_, v___x_253_);
v___x_255_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_254_);
v___x_256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__37));
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_208_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_Syntax_node3(v___x_208_, v___x_214_, v___x_247_, v___x_255_, v___x_257_);
v___x_259_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__39));
v___x_260_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__40));
v___x_261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_208_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__42));
v___x_263_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__43));
v___x_264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_208_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = l_Lean_Syntax_node1(v___x_208_, v___x_262_, v___x_264_);
v___x_266_ = l_Lean_Syntax_node2(v___x_208_, v___x_259_, v___x_261_, v___x_265_);
v___x_267_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_266_);
lean_inc(v___x_242_);
v___x_268_ = l_Lean_Syntax_node6(v___x_208_, v___x_239_, v___x_240_, v___x_242_, v___x_220_, v___x_245_, v___x_258_, v___x_267_);
v___x_269_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_268_);
v___x_270_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_269_);
v___x_271_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_270_);
lean_inc_ref_n(v___x_237_, 2);
v___x_272_ = l_Lean_Syntax_node2(v___x_208_, v___x_235_, v___x_237_, v___x_271_);
lean_inc(v___x_272_);
v___x_273_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_272_);
v___x_274_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_273_);
v___x_275_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_274_);
lean_inc_ref_n(v___x_234_, 3);
v___x_276_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_275_);
v___x_277_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__45));
v___x_278_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__46));
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_208_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__47));
v___x_281_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__48));
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_208_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
v___x_283_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__50));
v___x_284_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__52));
v___x_285_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__53));
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_208_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__55));
v___x_288_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__58));
v___x_289_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__59));
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_208_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_Syntax_node1(v___x_208_, v___x_288_, v___x_290_);
v___x_292_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__60));
v___x_293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_208_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_inc(v___x_291_);
v___x_294_ = l_Lean_Syntax_node3(v___x_208_, v___x_287_, v___x_291_, v___x_293_, v___x_291_);
v___x_295_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__61));
v___x_296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_208_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_Syntax_node3(v___x_208_, v___x_284_, v___x_286_, v___x_294_, v___x_296_);
v___x_298_ = l_Lean_Syntax_node2(v___x_208_, v___x_283_, v___x_220_, v___x_297_);
v___x_299_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_298_);
v___x_300_ = l_Lean_Syntax_node4(v___x_208_, v___x_281_, v___x_282_, v___x_299_, v___x_220_, v___x_220_);
v___x_301_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_300_);
v___x_302_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_301_);
v___x_303_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_302_);
v___x_304_ = l_Lean_Syntax_node2(v___x_208_, v___x_277_, v___x_279_, v___x_303_);
v___x_305_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__62));
v___x_306_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__63));
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_208_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
v___x_308_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__65);
v___x_309_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__68));
v___x_310_ = l_Lean_addMacroScope(v_quotContext_204_, v___x_309_, v_currMacroScope_205_);
v___x_311_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__70));
v___x_312_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_312_, 0, v___x_208_);
lean_ctor_set(v___x_312_, 1, v___x_308_);
lean_ctor_set(v___x_312_, 2, v___x_310_);
lean_ctor_set(v___x_312_, 3, v___x_311_);
v___x_313_ = l_Lean_Syntax_node2(v___x_208_, v___x_306_, v___x_307_, v___x_312_);
v___x_314_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_313_);
v___x_315_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_314_);
v___x_316_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_315_);
v___x_317_ = l_Lean_Syntax_node2(v___x_208_, v___x_222_, v___x_223_, v___x_316_);
v___x_318_ = l_Lean_Syntax_node5(v___x_208_, v___x_214_, v___x_272_, v___x_220_, v___x_304_, v___x_220_, v___x_317_);
v___x_319_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_318_);
v___x_320_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_319_);
v___x_321_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_320_);
v___x_322_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__71));
v___x_323_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__72));
v___x_324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_208_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
v___x_325_ = l_Lean_Syntax_node1(v___x_208_, v___x_323_, v___x_324_);
v___x_326_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_325_);
v___x_327_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_326_);
v___x_328_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_327_);
v___x_329_ = l_Lean_Syntax_node2(v___x_208_, v___x_235_, v___x_237_, v___x_328_);
v___x_330_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__73));
v___x_331_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__74));
v___x_332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_208_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
v___x_333_ = l_Lean_Syntax_node1(v___x_208_, v___x_331_, v___x_332_);
v___x_334_ = l_Lean_Syntax_node1(v___x_208_, v___x_214_, v___x_333_);
v___x_335_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_334_);
v___x_336_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_335_);
v___x_337_ = l_Lean_Syntax_node2(v___x_208_, v___x_235_, v___x_237_, v___x_336_);
v___x_338_ = l_Lean_Syntax_node3(v___x_208_, v___x_214_, v___x_329_, v___x_220_, v___x_337_);
v___x_339_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_338_);
v___x_340_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_339_);
v___x_341_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_340_);
v___x_342_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__75));
v___x_343_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__76));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_208_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
v___x_345_ = l_Lean_Syntax_node2(v___x_208_, v___x_343_, v___x_344_, v___x_242_);
lean_inc(v___x_218_);
v___x_346_ = l_Lean_Syntax_node3(v___x_208_, v___x_214_, v___x_218_, v___x_220_, v___x_345_);
v___x_347_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_347_);
v___x_349_ = l_Lean_Syntax_node2(v___x_208_, v___x_232_, v___x_234_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(12u);
v___x_351_ = lean_mk_empty_array_with_capacity(v___x_350_);
v___x_352_ = lean_array_push(v___x_351_, v___x_218_);
v___x_353_ = lean_array_push(v___x_352_, v___x_220_);
v___x_354_ = lean_array_push(v___x_353_, v___x_231_);
v___x_355_ = lean_array_push(v___x_354_, v___x_220_);
v___x_356_ = lean_array_push(v___x_355_, v___x_276_);
v___x_357_ = lean_array_push(v___x_356_, v___x_220_);
v___x_358_ = lean_array_push(v___x_357_, v___x_321_);
v___x_359_ = lean_array_push(v___x_358_, v___x_220_);
v___x_360_ = lean_array_push(v___x_359_, v___x_341_);
v___x_361_ = lean_array_push(v___x_360_, v___x_220_);
v___x_362_ = lean_array_push(v___x_361_, v___x_349_);
v___x_363_ = lean_array_push(v___x_362_, v___x_220_);
v___x_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_208_);
lean_ctor_set(v___x_364_, 1, v___x_214_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
v___x_365_ = l_Lean_Syntax_node1(v___x_208_, v___x_213_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node1(v___x_208_, v___x_212_, v___x_365_);
v___x_367_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__77));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___boxed(lean_object* v_x_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1(v_x_371_, v_a_372_, v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1(lean_object* v_x_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term_u2713___closed__1));
v___x_408_ = l_Lean_Syntax_isOfKind(v_x_404_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_box(1);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_a_406_);
return v___x_410_;
}
else
{
lean_object* v_ref_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_ref_411_ = lean_ctor_get(v_a_405_, 5);
v___x_412_ = 0;
v___x_413_ = l_Lean_SourceInfo_fromRef(v_ref_411_, v___x_412_);
v___x_414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__1));
v___x_415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__2));
lean_inc_n(v___x_413_, 12);
v___x_416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_413_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__7));
v___x_418_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__9));
v___x_419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__tacticTree__tac__1___closed__11));
v___x_420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__3));
v___x_421_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__4));
v___x_422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_413_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
v___x_423_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___closed__5));
v___x_424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_413_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__5));
v___x_426_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_tacticTree__tac___closed__6));
v___x_427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_413_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_Syntax_node1(v___x_413_, v___x_425_, v___x_427_);
v___x_429_ = l_Lean_Syntax_node1(v___x_413_, v___x_419_, v___x_428_);
v___x_430_ = l_Lean_Syntax_node1(v___x_413_, v___x_418_, v___x_429_);
v___x_431_ = l_Lean_Syntax_node1(v___x_413_, v___x_417_, v___x_430_);
v___x_432_ = l_Lean_Syntax_node3(v___x_413_, v___x_421_, v___x_422_, v___x_424_, v___x_431_);
v___x_433_ = l_Lean_Syntax_node1(v___x_413_, v___x_419_, v___x_432_);
v___x_434_ = l_Lean_Syntax_node1(v___x_413_, v___x_418_, v___x_433_);
v___x_435_ = l_Lean_Syntax_node1(v___x_413_, v___x_417_, v___x_434_);
v___x_436_ = l_Lean_Syntax_node2(v___x_413_, v___x_414_, v___x_416_, v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_a_406_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1___boxed(lean_object* v_x_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Balancing______macroRules__Std__DTreeMap__Internal__Impl__term_u2713__1(v_x_438_, v_a_439_, v_a_440_);
lean_dec_ref(v_a_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL___redArg(lean_object* v_k_442_, lean_object* v_v_443_, lean_object* v_l_444_, lean_object* v_r_445_){
_start:
{
if (lean_obj_tag(v_r_445_) == 0)
{
if (lean_obj_tag(v_l_444_) == 0)
{
lean_object* v_size_446_; lean_object* v_size_447_; lean_object* v_k_448_; lean_object* v_v_449_; lean_object* v_l_450_; lean_object* v_r_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_size_446_ = lean_ctor_get(v_r_445_, 0);
v_size_447_ = lean_ctor_get(v_l_444_, 0);
v_k_448_ = lean_ctor_get(v_l_444_, 1);
v_v_449_ = lean_ctor_get(v_l_444_, 2);
v_l_450_ = lean_ctor_get(v_l_444_, 3);
v_r_451_ = lean_ctor_get(v_l_444_, 4);
lean_inc(v_r_451_);
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = lean_nat_mul(v___x_452_, v_size_446_);
v___x_454_ = lean_nat_dec_lt(v___x_453_, v_size_447_);
lean_dec(v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_r_451_);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v___x_455_, v_size_447_);
v___x_457_ = lean_nat_add(v___x_456_, v_size_446_);
lean_dec(v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v_k_442_);
lean_ctor_set(v___x_458_, 2, v_v_443_);
lean_ctor_set(v___x_458_, 3, v_l_444_);
lean_ctor_set(v___x_458_, 4, v_r_445_);
return v___x_458_;
}
else
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_524_; 
lean_inc(v_l_450_);
lean_inc(v_v_449_);
lean_inc(v_k_448_);
lean_inc(v_size_447_);
v_isSharedCheck_524_ = !lean_is_exclusive(v_l_444_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; lean_object* v_unused_526_; lean_object* v_unused_527_; lean_object* v_unused_528_; lean_object* v_unused_529_; 
v_unused_525_ = lean_ctor_get(v_l_444_, 4);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_l_444_, 3);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_l_444_, 2);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_l_444_, 1);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_l_444_, 0);
lean_dec(v_unused_529_);
v___x_460_ = v_l_444_;
v_isShared_461_ = v_isSharedCheck_524_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_l_444_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_524_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_size_462_; lean_object* v_size_463_; lean_object* v_k_464_; lean_object* v_v_465_; lean_object* v_l_466_; lean_object* v_r_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_size_462_ = lean_ctor_get(v_l_450_, 0);
v_size_463_ = lean_ctor_get(v_r_451_, 0);
v_k_464_ = lean_ctor_get(v_r_451_, 1);
v_v_465_ = lean_ctor_get(v_r_451_, 2);
v_l_466_ = lean_ctor_get(v_r_451_, 3);
v_r_467_ = lean_ctor_get(v_r_451_, 4);
v___x_468_ = lean_unsigned_to_nat(2u);
v___x_469_ = lean_nat_mul(v___x_468_, v_size_462_);
v___x_470_ = lean_nat_dec_lt(v_size_463_, v___x_469_);
lean_dec(v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_498_; 
lean_inc(v_r_467_);
lean_inc(v_l_466_);
lean_inc(v_v_465_);
lean_inc(v_k_464_);
v_isSharedCheck_498_ = !lean_is_exclusive(v_r_451_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; lean_object* v_unused_500_; lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_499_ = lean_ctor_get(v_r_451_, 4);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_r_451_, 3);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_r_451_, 2);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_r_451_, 1);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_r_451_, 0);
lean_dec(v_unused_503_);
v___x_472_ = v_r_451_;
v_isShared_473_ = v_isSharedCheck_498_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_r_451_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_498_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___x_488_; lean_object* v___y_490_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_add(v___x_474_, v_size_447_);
lean_dec(v_size_447_);
v___x_476_ = lean_nat_add(v___x_475_, v_size_446_);
lean_dec(v___x_475_);
v___x_488_ = lean_nat_add(v___x_474_, v_size_462_);
if (lean_obj_tag(v_l_466_) == 0)
{
lean_object* v_size_496_; 
v_size_496_ = lean_ctor_get(v_l_466_, 0);
lean_inc(v_size_496_);
v___y_490_ = v_size_496_;
goto v___jp_489_;
}
else
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___y_490_ = v___x_497_;
goto v___jp_489_;
}
v___jp_477_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_nat_add(v___y_478_, v___y_480_);
lean_dec(v___y_480_);
lean_dec(v___y_478_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 4, v_r_445_);
lean_ctor_set(v___x_472_, 3, v_r_467_);
lean_ctor_set(v___x_472_, 2, v_v_443_);
lean_ctor_set(v___x_472_, 1, v_k_442_);
lean_ctor_set(v___x_472_, 0, v___x_481_);
v___x_483_ = v___x_472_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_r_467_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v_r_445_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 4, v___x_483_);
lean_ctor_set(v___x_460_, 3, v___y_479_);
lean_ctor_set(v___x_460_, 2, v_v_465_);
lean_ctor_set(v___x_460_, 1, v_k_464_);
lean_ctor_set(v___x_460_, 0, v___x_476_);
v___x_485_ = v___x_460_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v___y_479_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_nat_add(v___x_488_, v___y_490_);
lean_dec(v___y_490_);
lean_dec(v___x_488_);
v___x_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_k_448_);
lean_ctor_set(v___x_492_, 2, v_v_449_);
lean_ctor_set(v___x_492_, 3, v_l_450_);
lean_ctor_set(v___x_492_, 4, v_l_466_);
v___x_493_ = lean_nat_add(v___x_474_, v_size_446_);
if (lean_obj_tag(v_r_467_) == 0)
{
lean_object* v_size_494_; 
v_size_494_ = lean_ctor_get(v_r_467_, 0);
lean_inc(v_size_494_);
v___y_478_ = v___x_493_;
v___y_479_ = v___x_492_;
v___y_480_ = v_size_494_;
goto v___jp_477_;
}
else
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___y_478_ = v___x_493_;
v___y_479_ = v___x_492_;
v___y_480_ = v___x_495_;
goto v___jp_477_;
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v___x_504_, v_size_447_);
lean_dec(v_size_447_);
v___x_506_ = lean_nat_add(v___x_505_, v_size_446_);
lean_dec(v___x_505_);
v___x_507_ = lean_nat_add(v___x_504_, v_size_446_);
v___x_508_ = lean_nat_add(v___x_507_, v_size_463_);
lean_dec(v___x_507_);
lean_inc_ref(v_r_445_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 4, v_r_445_);
lean_ctor_set(v___x_460_, 3, v_r_451_);
lean_ctor_set(v___x_460_, 2, v_v_443_);
lean_ctor_set(v___x_460_, 1, v_k_442_);
lean_ctor_set(v___x_460_, 0, v___x_508_);
v___x_510_ = v___x_460_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_r_451_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_r_445_);
v___x_510_ = v_reuseFailAlloc_523_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v_r_445_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; lean_object* v_unused_522_; 
v_unused_518_ = lean_ctor_get(v_r_445_, 4);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_r_445_, 3);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_r_445_, 2);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_r_445_, 1);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_r_445_, 0);
lean_dec(v_unused_522_);
v___x_512_ = v_r_445_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_dec(v_r_445_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_510_);
lean_ctor_set(v___x_512_, 3, v_l_450_);
lean_ctor_set(v___x_512_, 2, v_v_449_);
lean_ctor_set(v___x_512_, 1, v_k_448_);
lean_ctor_set(v___x_512_, 0, v___x_506_);
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_l_450_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v___x_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_size_530_ = lean_ctor_get(v_r_445_, 0);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v___x_531_, v_size_530_);
v___x_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_k_442_);
lean_ctor_set(v___x_533_, 2, v_v_443_);
lean_ctor_set(v___x_533_, 3, v_l_444_);
lean_ctor_set(v___x_533_, 4, v_r_445_);
return v___x_533_;
}
}
else
{
if (lean_obj_tag(v_l_444_) == 0)
{
lean_object* v_l_534_; 
v_l_534_ = lean_ctor_get(v_l_444_, 3);
if (lean_obj_tag(v_l_534_) == 0)
{
lean_object* v_r_535_; lean_object* v_k_536_; lean_object* v_v_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_547_; 
lean_inc_ref(v_l_534_);
v_r_535_ = lean_ctor_get(v_l_444_, 4);
v_k_536_ = lean_ctor_get(v_l_444_, 1);
v_v_537_ = lean_ctor_get(v_l_444_, 2);
v_isSharedCheck_547_ = !lean_is_exclusive(v_l_444_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; 
v_unused_548_ = lean_ctor_get(v_l_444_, 3);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_l_444_, 0);
lean_dec(v_unused_549_);
v___x_539_ = v_l_444_;
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_r_535_);
lean_inc(v_v_537_);
lean_inc(v_k_536_);
lean_dec(v_l_444_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_unsigned_to_nat(3u);
v___x_542_ = lean_unsigned_to_nat(1u);
lean_inc(v_r_535_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 3, v_r_535_);
lean_ctor_set(v___x_539_, 2, v_v_443_);
lean_ctor_set(v___x_539_, 1, v_k_442_);
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_r_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_r_535_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_545_, 0, v___x_541_);
lean_ctor_set(v___x_545_, 1, v_k_536_);
lean_ctor_set(v___x_545_, 2, v_v_537_);
lean_ctor_set(v___x_545_, 3, v_l_534_);
lean_ctor_set(v___x_545_, 4, v___x_544_);
return v___x_545_;
}
}
}
else
{
lean_object* v_r_550_; 
v_r_550_ = lean_ctor_get(v_l_444_, 4);
lean_inc(v_r_550_);
if (lean_obj_tag(v_r_550_) == 0)
{
lean_object* v_k_551_; lean_object* v_v_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_574_; 
lean_inc(v_l_534_);
v_k_551_ = lean_ctor_get(v_l_444_, 1);
v_v_552_ = lean_ctor_get(v_l_444_, 2);
v_isSharedCheck_574_ = !lean_is_exclusive(v_l_444_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; lean_object* v_unused_576_; lean_object* v_unused_577_; 
v_unused_575_ = lean_ctor_get(v_l_444_, 4);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_l_444_, 3);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_l_444_, 0);
lean_dec(v_unused_577_);
v___x_554_ = v_l_444_;
v_isShared_555_ = v_isSharedCheck_574_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_v_552_);
lean_inc(v_k_551_);
lean_dec(v_l_444_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_574_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_k_556_; lean_object* v_v_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_570_; 
v_k_556_ = lean_ctor_get(v_r_550_, 1);
v_v_557_ = lean_ctor_get(v_r_550_, 2);
v_isSharedCheck_570_ = !lean_is_exclusive(v_r_550_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_571_ = lean_ctor_get(v_r_550_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_550_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_r_550_, 0);
lean_dec(v_unused_573_);
v___x_559_ = v_r_550_;
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_v_557_);
lean_inc(v_k_556_);
lean_dec(v_r_550_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = lean_unsigned_to_nat(3u);
v___x_562_ = lean_unsigned_to_nat(1u);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 4, v_l_534_);
lean_ctor_set(v___x_559_, 3, v_l_534_);
lean_ctor_set(v___x_559_, 2, v_v_552_);
lean_ctor_set(v___x_559_, 1, v_k_551_);
lean_ctor_set(v___x_559_, 0, v___x_562_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_k_551_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_v_552_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_l_534_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_l_534_);
v___x_564_ = v_reuseFailAlloc_569_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 4, v_l_534_);
lean_ctor_set(v___x_554_, 2, v_v_443_);
lean_ctor_set(v___x_554_, 1, v_k_442_);
lean_ctor_set(v___x_554_, 0, v___x_562_);
v___x_566_ = v___x_554_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_l_534_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_l_534_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_567_, 0, v___x_561_);
lean_ctor_set(v___x_567_, 1, v_k_556_);
lean_ctor_set(v___x_567_, 2, v_v_557_);
lean_ctor_set(v___x_567_, 3, v___x_564_);
lean_ctor_set(v___x_567_, 4, v___x_566_);
return v___x_567_;
}
}
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_k_442_);
lean_ctor_set(v___x_579_, 2, v_v_443_);
lean_ctor_set(v___x_579_, 3, v_l_444_);
lean_ctor_set(v___x_579_, 4, v_r_550_);
return v___x_579_;
}
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_k_442_);
lean_ctor_set(v___x_581_, 2, v_v_443_);
lean_ctor_set(v___x_581_, 3, v_l_444_);
lean_ctor_set(v___x_581_, 4, v_l_444_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_k_584_, lean_object* v_v_585_, lean_object* v_l_586_, lean_object* v_r_587_, lean_object* v_hlb_588_, lean_object* v_hrb_589_, lean_object* v_hlr_590_){
_start:
{
if (lean_obj_tag(v_r_587_) == 0)
{
if (lean_obj_tag(v_l_586_) == 0)
{
lean_object* v_size_591_; lean_object* v_size_592_; lean_object* v_k_593_; lean_object* v_v_594_; lean_object* v_l_595_; lean_object* v_r_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_size_591_ = lean_ctor_get(v_r_587_, 0);
v_size_592_ = lean_ctor_get(v_l_586_, 0);
v_k_593_ = lean_ctor_get(v_l_586_, 1);
v_v_594_ = lean_ctor_get(v_l_586_, 2);
v_l_595_ = lean_ctor_get(v_l_586_, 3);
v_r_596_ = lean_ctor_get(v_l_586_, 4);
lean_inc(v_r_596_);
v___x_597_ = lean_unsigned_to_nat(3u);
v___x_598_ = lean_nat_mul(v___x_597_, v_size_591_);
v___x_599_ = lean_nat_dec_lt(v___x_598_, v_size_592_);
lean_dec(v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_r_596_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v___x_600_, v_size_592_);
v___x_602_ = lean_nat_add(v___x_601_, v_size_591_);
lean_dec(v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v_k_584_);
lean_ctor_set(v___x_603_, 2, v_v_585_);
lean_ctor_set(v___x_603_, 3, v_l_586_);
lean_ctor_set(v___x_603_, 4, v_r_587_);
return v___x_603_;
}
else
{
lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_669_; 
lean_inc(v_l_595_);
lean_inc(v_v_594_);
lean_inc(v_k_593_);
lean_inc(v_size_592_);
v_isSharedCheck_669_ = !lean_is_exclusive(v_l_586_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; lean_object* v_unused_673_; lean_object* v_unused_674_; 
v_unused_670_ = lean_ctor_get(v_l_586_, 4);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_l_586_, 3);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_l_586_, 2);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_l_586_, 1);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_l_586_, 0);
lean_dec(v_unused_674_);
v___x_605_ = v_l_586_;
v_isShared_606_ = v_isSharedCheck_669_;
goto v_resetjp_604_;
}
else
{
lean_dec(v_l_586_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_669_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_size_607_; lean_object* v_size_608_; lean_object* v_k_609_; lean_object* v_v_610_; lean_object* v_l_611_; lean_object* v_r_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_size_607_ = lean_ctor_get(v_l_595_, 0);
v_size_608_ = lean_ctor_get(v_r_596_, 0);
v_k_609_ = lean_ctor_get(v_r_596_, 1);
v_v_610_ = lean_ctor_get(v_r_596_, 2);
v_l_611_ = lean_ctor_get(v_r_596_, 3);
v_r_612_ = lean_ctor_get(v_r_596_, 4);
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = lean_nat_mul(v___x_613_, v_size_607_);
v___x_615_ = lean_nat_dec_lt(v_size_608_, v___x_614_);
lean_dec(v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_643_; 
lean_inc(v_r_612_);
lean_inc(v_l_611_);
lean_inc(v_v_610_);
lean_inc(v_k_609_);
v_isSharedCheck_643_ = !lean_is_exclusive(v_r_596_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_644_ = lean_ctor_get(v_r_596_, 4);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_r_596_, 3);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_r_596_, 2);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_r_596_, 1);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_r_596_, 0);
lean_dec(v_unused_648_);
v___x_617_ = v_r_596_;
v_isShared_618_ = v_isSharedCheck_643_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_r_596_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_643_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___x_633_; lean_object* v___y_635_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_add(v___x_619_, v_size_592_);
lean_dec(v_size_592_);
v___x_621_ = lean_nat_add(v___x_620_, v_size_591_);
lean_dec(v___x_620_);
v___x_633_ = lean_nat_add(v___x_619_, v_size_607_);
if (lean_obj_tag(v_l_611_) == 0)
{
lean_object* v_size_641_; 
v_size_641_ = lean_ctor_get(v_l_611_, 0);
lean_inc(v_size_641_);
v___y_635_ = v_size_641_;
goto v___jp_634_;
}
else
{
lean_object* v___x_642_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___y_635_ = v___x_642_;
goto v___jp_634_;
}
v___jp_622_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_nat_add(v___y_623_, v___y_625_);
lean_dec(v___y_625_);
lean_dec(v___y_623_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v_r_587_);
lean_ctor_set(v___x_617_, 3, v_r_612_);
lean_ctor_set(v___x_617_, 2, v_v_585_);
lean_ctor_set(v___x_617_, 1, v_k_584_);
lean_ctor_set(v___x_617_, 0, v___x_626_);
v___x_628_ = v___x_617_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_r_612_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_r_587_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v___x_628_);
lean_ctor_set(v___x_605_, 3, v___y_624_);
lean_ctor_set(v___x_605_, 2, v_v_610_);
lean_ctor_set(v___x_605_, 1, v_k_609_);
lean_ctor_set(v___x_605_, 0, v___x_621_);
v___x_630_ = v___x_605_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_k_609_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_v_610_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v___y_624_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_nat_add(v___x_633_, v___y_635_);
lean_dec(v___y_635_);
lean_dec(v___x_633_);
v___x_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_k_593_);
lean_ctor_set(v___x_637_, 2, v_v_594_);
lean_ctor_set(v___x_637_, 3, v_l_595_);
lean_ctor_set(v___x_637_, 4, v_l_611_);
v___x_638_ = lean_nat_add(v___x_619_, v_size_591_);
if (lean_obj_tag(v_r_612_) == 0)
{
lean_object* v_size_639_; 
v_size_639_ = lean_ctor_get(v_r_612_, 0);
lean_inc(v_size_639_);
v___y_623_ = v___x_638_;
v___y_624_ = v___x_637_;
v___y_625_ = v_size_639_;
goto v___jp_622_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___y_623_ = v___x_638_;
v___y_624_ = v___x_637_;
v___y_625_ = v___x_640_;
goto v___jp_622_;
}
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v___x_649_, v_size_592_);
lean_dec(v_size_592_);
v___x_651_ = lean_nat_add(v___x_650_, v_size_591_);
lean_dec(v___x_650_);
v___x_652_ = lean_nat_add(v___x_649_, v_size_591_);
v___x_653_ = lean_nat_add(v___x_652_, v_size_608_);
lean_dec(v___x_652_);
lean_inc_ref(v_r_587_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v_r_587_);
lean_ctor_set(v___x_605_, 3, v_r_596_);
lean_ctor_set(v___x_605_, 2, v_v_585_);
lean_ctor_set(v___x_605_, 1, v_k_584_);
lean_ctor_set(v___x_605_, 0, v___x_653_);
v___x_655_ = v___x_605_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_r_596_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_r_587_);
v___x_655_ = v_reuseFailAlloc_668_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
v_isSharedCheck_662_ = !lean_is_exclusive(v_r_587_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; lean_object* v_unused_664_; lean_object* v_unused_665_; lean_object* v_unused_666_; lean_object* v_unused_667_; 
v_unused_663_ = lean_ctor_get(v_r_587_, 4);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v_r_587_, 3);
lean_dec(v_unused_664_);
v_unused_665_ = lean_ctor_get(v_r_587_, 2);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_r_587_, 1);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_r_587_, 0);
lean_dec(v_unused_667_);
v___x_657_ = v_r_587_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_r_587_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___x_655_);
lean_ctor_set(v___x_657_, 3, v_l_595_);
lean_ctor_set(v___x_657_, 2, v_v_594_);
lean_ctor_set(v___x_657_, 1, v_k_593_);
lean_ctor_set(v___x_657_, 0, v___x_651_);
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_k_593_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_v_594_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_l_595_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v___x_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_size_675_ = lean_ctor_get(v_r_587_, 0);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v___x_676_, v_size_675_);
v___x_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_k_584_);
lean_ctor_set(v___x_678_, 2, v_v_585_);
lean_ctor_set(v___x_678_, 3, v_l_586_);
lean_ctor_set(v___x_678_, 4, v_r_587_);
return v___x_678_;
}
}
else
{
if (lean_obj_tag(v_l_586_) == 0)
{
lean_object* v_l_679_; 
v_l_679_ = lean_ctor_get(v_l_586_, 3);
if (lean_obj_tag(v_l_679_) == 0)
{
lean_object* v_r_680_; lean_object* v_k_681_; lean_object* v_v_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
lean_inc_ref(v_l_679_);
v_r_680_ = lean_ctor_get(v_l_586_, 4);
v_k_681_ = lean_ctor_get(v_l_586_, 1);
v_v_682_ = lean_ctor_get(v_l_586_, 2);
v_isSharedCheck_692_ = !lean_is_exclusive(v_l_586_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; lean_object* v_unused_694_; 
v_unused_693_ = lean_ctor_get(v_l_586_, 3);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_l_586_, 0);
lean_dec(v_unused_694_);
v___x_684_ = v_l_586_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_r_680_);
lean_inc(v_v_682_);
lean_inc(v_k_681_);
lean_dec(v_l_586_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_686_ = lean_unsigned_to_nat(3u);
v___x_687_ = lean_unsigned_to_nat(1u);
lean_inc(v_r_680_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 3, v_r_680_);
lean_ctor_set(v___x_684_, 2, v_v_585_);
lean_ctor_set(v___x_684_, 1, v_k_584_);
lean_ctor_set(v___x_684_, 0, v___x_687_);
v___x_689_ = v___x_684_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_r_680_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_r_680_);
v___x_689_ = v_reuseFailAlloc_691_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; 
v___x_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_690_, 0, v___x_686_);
lean_ctor_set(v___x_690_, 1, v_k_681_);
lean_ctor_set(v___x_690_, 2, v_v_682_);
lean_ctor_set(v___x_690_, 3, v_l_679_);
lean_ctor_set(v___x_690_, 4, v___x_689_);
return v___x_690_;
}
}
}
else
{
lean_object* v_r_695_; 
v_r_695_ = lean_ctor_get(v_l_586_, 4);
lean_inc(v_r_695_);
if (lean_obj_tag(v_r_695_) == 0)
{
lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_719_; 
lean_inc(v_l_679_);
v_k_696_ = lean_ctor_get(v_l_586_, 1);
v_v_697_ = lean_ctor_get(v_l_586_, 2);
v_isSharedCheck_719_ = !lean_is_exclusive(v_l_586_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; 
v_unused_720_ = lean_ctor_get(v_l_586_, 4);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_l_586_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_l_586_, 0);
lean_dec(v_unused_722_);
v___x_699_ = v_l_586_;
v_isShared_700_ = v_isSharedCheck_719_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_dec(v_l_586_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_719_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_715_; 
v_k_701_ = lean_ctor_get(v_r_695_, 1);
v_v_702_ = lean_ctor_get(v_r_695_, 2);
v_isSharedCheck_715_ = !lean_is_exclusive(v_r_695_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_716_ = lean_ctor_get(v_r_695_, 4);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_r_695_, 3);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_r_695_, 0);
lean_dec(v_unused_718_);
v___x_704_ = v_r_695_;
v_isShared_705_ = v_isSharedCheck_715_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_v_702_);
lean_inc(v_k_701_);
lean_dec(v_r_695_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_715_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = lean_unsigned_to_nat(3u);
v___x_707_ = lean_unsigned_to_nat(1u);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 4, v_l_679_);
lean_ctor_set(v___x_704_, 3, v_l_679_);
lean_ctor_set(v___x_704_, 2, v_v_697_);
lean_ctor_set(v___x_704_, 1, v_k_696_);
lean_ctor_set(v___x_704_, 0, v___x_707_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_l_679_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_l_679_);
v___x_709_ = v_reuseFailAlloc_714_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 4, v_l_679_);
lean_ctor_set(v___x_699_, 2, v_v_585_);
lean_ctor_set(v___x_699_, 1, v_k_584_);
lean_ctor_set(v___x_699_, 0, v___x_707_);
v___x_711_ = v___x_699_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_l_679_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_l_679_);
v___x_711_ = v_reuseFailAlloc_713_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_712_, 0, v___x_706_);
lean_ctor_set(v___x_712_, 1, v_k_701_);
lean_ctor_set(v___x_712_, 2, v_v_702_);
lean_ctor_set(v___x_712_, 3, v___x_709_);
lean_ctor_set(v___x_712_, 4, v___x_711_);
return v___x_712_;
}
}
}
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(2u);
v___x_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_k_584_);
lean_ctor_set(v___x_724_, 2, v_v_585_);
lean_ctor_set(v___x_724_, 3, v_l_586_);
lean_ctor_set(v___x_724_, 4, v_r_695_);
return v___x_724_;
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_k_584_);
lean_ctor_set(v___x_726_, 2, v_v_585_);
lean_ctor_set(v___x_726_, 3, v_l_586_);
lean_ctor_set(v___x_726_, 4, v_l_586_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase___redArg(lean_object* v_k_727_, lean_object* v_v_728_, lean_object* v_l_729_, lean_object* v_r_730_){
_start:
{
if (lean_obj_tag(v_r_730_) == 0)
{
if (lean_obj_tag(v_l_729_) == 0)
{
lean_object* v_size_731_; lean_object* v_size_732_; lean_object* v_k_733_; lean_object* v_v_734_; lean_object* v_l_735_; lean_object* v_r_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_size_731_ = lean_ctor_get(v_r_730_, 0);
v_size_732_ = lean_ctor_get(v_l_729_, 0);
v_k_733_ = lean_ctor_get(v_l_729_, 1);
v_v_734_ = lean_ctor_get(v_l_729_, 2);
v_l_735_ = lean_ctor_get(v_l_729_, 3);
v_r_736_ = lean_ctor_get(v_l_729_, 4);
lean_inc(v_r_736_);
v___x_737_ = lean_unsigned_to_nat(3u);
v___x_738_ = lean_nat_mul(v___x_737_, v_size_731_);
v___x_739_ = lean_nat_dec_lt(v___x_738_, v_size_732_);
lean_dec(v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v_r_736_);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v___x_740_, v_size_732_);
v___x_742_ = lean_nat_add(v___x_741_, v_size_731_);
lean_dec(v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_k_727_);
lean_ctor_set(v___x_743_, 2, v_v_728_);
lean_ctor_set(v___x_743_, 3, v_l_729_);
lean_ctor_set(v___x_743_, 4, v_r_730_);
return v___x_743_;
}
else
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_809_; 
lean_inc(v_l_735_);
lean_inc(v_v_734_);
lean_inc(v_k_733_);
lean_inc(v_size_732_);
v_isSharedCheck_809_ = !lean_is_exclusive(v_l_729_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; lean_object* v_unused_813_; lean_object* v_unused_814_; 
v_unused_810_ = lean_ctor_get(v_l_729_, 4);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_l_729_, 3);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_l_729_, 2);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_l_729_, 1);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_l_729_, 0);
lean_dec(v_unused_814_);
v___x_745_ = v_l_729_;
v_isShared_746_ = v_isSharedCheck_809_;
goto v_resetjp_744_;
}
else
{
lean_dec(v_l_729_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_809_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_size_747_; lean_object* v_size_748_; lean_object* v_k_749_; lean_object* v_v_750_; lean_object* v_l_751_; lean_object* v_r_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_size_747_ = lean_ctor_get(v_l_735_, 0);
v_size_748_ = lean_ctor_get(v_r_736_, 0);
v_k_749_ = lean_ctor_get(v_r_736_, 1);
v_v_750_ = lean_ctor_get(v_r_736_, 2);
v_l_751_ = lean_ctor_get(v_r_736_, 3);
v_r_752_ = lean_ctor_get(v_r_736_, 4);
v___x_753_ = lean_unsigned_to_nat(2u);
v___x_754_ = lean_nat_mul(v___x_753_, v_size_747_);
v___x_755_ = lean_nat_dec_lt(v_size_748_, v___x_754_);
lean_dec(v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_783_; 
lean_inc(v_r_752_);
lean_inc(v_l_751_);
lean_inc(v_v_750_);
lean_inc(v_k_749_);
v_isSharedCheck_783_ = !lean_is_exclusive(v_r_736_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; lean_object* v_unused_788_; 
v_unused_784_ = lean_ctor_get(v_r_736_, 4);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_r_736_, 3);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_r_736_, 2);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_r_736_, 1);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_r_736_, 0);
lean_dec(v_unused_788_);
v___x_757_ = v_r_736_;
v_isShared_758_ = v_isSharedCheck_783_;
goto v_resetjp_756_;
}
else
{
lean_dec(v_r_736_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_783_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___x_773_; lean_object* v___y_775_; 
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_add(v___x_759_, v_size_732_);
lean_dec(v_size_732_);
v___x_761_ = lean_nat_add(v___x_760_, v_size_731_);
lean_dec(v___x_760_);
v___x_773_ = lean_nat_add(v___x_759_, v_size_747_);
if (lean_obj_tag(v_l_751_) == 0)
{
lean_object* v_size_781_; 
v_size_781_ = lean_ctor_get(v_l_751_, 0);
lean_inc(v_size_781_);
v___y_775_ = v_size_781_;
goto v___jp_774_;
}
else
{
lean_object* v___x_782_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___y_775_ = v___x_782_;
goto v___jp_774_;
}
v___jp_762_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_nat_add(v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec(v___y_764_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 4, v_r_730_);
lean_ctor_set(v___x_757_, 3, v_r_752_);
lean_ctor_set(v___x_757_, 2, v_v_728_);
lean_ctor_set(v___x_757_, 1, v_k_727_);
lean_ctor_set(v___x_757_, 0, v___x_766_);
v___x_768_ = v___x_757_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_r_752_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_r_730_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 4, v___x_768_);
lean_ctor_set(v___x_745_, 3, v___y_763_);
lean_ctor_set(v___x_745_, 2, v_v_750_);
lean_ctor_set(v___x_745_, 1, v_k_749_);
lean_ctor_set(v___x_745_, 0, v___x_761_);
v___x_770_ = v___x_745_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_749_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_750_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v___y_763_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_nat_add(v___x_773_, v___y_775_);
lean_dec(v___y_775_);
lean_dec(v___x_773_);
v___x_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v_k_733_);
lean_ctor_set(v___x_777_, 2, v_v_734_);
lean_ctor_set(v___x_777_, 3, v_l_735_);
lean_ctor_set(v___x_777_, 4, v_l_751_);
v___x_778_ = lean_nat_add(v___x_759_, v_size_731_);
if (lean_obj_tag(v_r_752_) == 0)
{
lean_object* v_size_779_; 
v_size_779_ = lean_ctor_get(v_r_752_, 0);
lean_inc(v_size_779_);
v___y_763_ = v___x_777_;
v___y_764_ = v___x_778_;
v___y_765_ = v_size_779_;
goto v___jp_762_;
}
else
{
lean_object* v___x_780_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___y_763_ = v___x_777_;
v___y_764_ = v___x_778_;
v___y_765_ = v___x_780_;
goto v___jp_762_;
}
}
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v___x_789_, v_size_732_);
lean_dec(v_size_732_);
v___x_791_ = lean_nat_add(v___x_790_, v_size_731_);
lean_dec(v___x_790_);
v___x_792_ = lean_nat_add(v___x_789_, v_size_731_);
v___x_793_ = lean_nat_add(v___x_792_, v_size_748_);
lean_dec(v___x_792_);
lean_inc_ref(v_r_730_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 4, v_r_730_);
lean_ctor_set(v___x_745_, 3, v_r_736_);
lean_ctor_set(v___x_745_, 2, v_v_728_);
lean_ctor_set(v___x_745_, 1, v_k_727_);
lean_ctor_set(v___x_745_, 0, v___x_793_);
v___x_795_ = v___x_745_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_r_736_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_r_730_);
v___x_795_ = v_reuseFailAlloc_808_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_isSharedCheck_802_ = !lean_is_exclusive(v_r_730_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; 
v_unused_803_ = lean_ctor_get(v_r_730_, 4);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_r_730_, 3);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_r_730_, 2);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_r_730_, 1);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_r_730_, 0);
lean_dec(v_unused_807_);
v___x_797_ = v_r_730_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_r_730_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 4, v___x_795_);
lean_ctor_set(v___x_797_, 3, v_l_735_);
lean_ctor_set(v___x_797_, 2, v_v_734_);
lean_ctor_set(v___x_797_, 1, v_k_733_);
lean_ctor_set(v___x_797_, 0, v___x_791_);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v___x_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_size_815_ = lean_ctor_get(v_r_730_, 0);
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v___x_816_, v_size_815_);
v___x_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_k_727_);
lean_ctor_set(v___x_818_, 2, v_v_728_);
lean_ctor_set(v___x_818_, 3, v_l_729_);
lean_ctor_set(v___x_818_, 4, v_r_730_);
return v___x_818_;
}
}
else
{
if (lean_obj_tag(v_l_729_) == 0)
{
lean_object* v_l_819_; 
v_l_819_ = lean_ctor_get(v_l_729_, 3);
if (lean_obj_tag(v_l_819_) == 0)
{
lean_object* v_r_820_; 
lean_inc_ref(v_l_819_);
v_r_820_ = lean_ctor_get(v_l_729_, 4);
lean_inc(v_r_820_);
if (lean_obj_tag(v_r_820_) == 0)
{
lean_object* v_size_821_; lean_object* v_k_822_; lean_object* v_v_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_846_; 
v_size_821_ = lean_ctor_get(v_l_729_, 0);
v_k_822_ = lean_ctor_get(v_l_729_, 1);
v_v_823_ = lean_ctor_get(v_l_729_, 2);
v_isSharedCheck_846_ = !lean_is_exclusive(v_l_729_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; 
v_unused_847_ = lean_ctor_get(v_l_729_, 4);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_l_729_, 3);
lean_dec(v_unused_848_);
v___x_825_ = v_l_729_;
v_isShared_826_ = v_isSharedCheck_846_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_v_823_);
lean_inc(v_k_822_);
lean_inc(v_size_821_);
lean_dec(v_l_729_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_846_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_size_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v_size_827_ = lean_ctor_get(v_r_820_, 0);
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_nat_add(v___x_828_, v_size_821_);
lean_dec(v_size_821_);
v___x_830_ = lean_nat_add(v___x_828_, v_size_827_);
lean_inc_ref(v_r_820_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 4, v_r_730_);
lean_ctor_set(v___x_825_, 3, v_r_820_);
lean_ctor_set(v___x_825_, 2, v_v_728_);
lean_ctor_set(v___x_825_, 1, v_k_727_);
lean_ctor_set(v___x_825_, 0, v___x_830_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_r_820_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_r_730_);
v___x_832_ = v_reuseFailAlloc_845_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_isSharedCheck_839_ = !lean_is_exclusive(v_r_820_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_840_ = lean_ctor_get(v_r_820_, 4);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_r_820_, 3);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_r_820_, 2);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_r_820_, 1);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_r_820_, 0);
lean_dec(v_unused_844_);
v___x_834_ = v_r_820_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_r_820_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v___x_832_);
lean_ctor_set(v___x_834_, 3, v_l_819_);
lean_ctor_set(v___x_834_, 2, v_v_823_);
lean_ctor_set(v___x_834_, 1, v_k_822_);
lean_ctor_set(v___x_834_, 0, v___x_829_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_k_822_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_v_823_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_l_819_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v___x_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
else
{
lean_object* v_k_849_; lean_object* v_v_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_k_849_ = lean_ctor_get(v_l_729_, 1);
v_v_850_ = lean_ctor_get(v_l_729_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_l_729_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; lean_object* v_unused_862_; lean_object* v_unused_863_; 
v_unused_861_ = lean_ctor_get(v_l_729_, 4);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_l_729_, 3);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_l_729_, 0);
lean_dec(v_unused_863_);
v___x_852_ = v_l_729_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_v_850_);
lean_inc(v_k_849_);
lean_dec(v_l_729_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = lean_unsigned_to_nat(3u);
v___x_855_ = lean_unsigned_to_nat(1u);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 3, v_r_820_);
lean_ctor_set(v___x_852_, 2, v_v_728_);
lean_ctor_set(v___x_852_, 1, v_k_727_);
lean_ctor_set(v___x_852_, 0, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v_r_820_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_r_820_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_858_, 0, v___x_854_);
lean_ctor_set(v___x_858_, 1, v_k_849_);
lean_ctor_set(v___x_858_, 2, v_v_850_);
lean_ctor_set(v___x_858_, 3, v_l_819_);
lean_ctor_set(v___x_858_, 4, v___x_857_);
return v___x_858_;
}
}
}
}
else
{
lean_object* v_r_864_; 
v_r_864_ = lean_ctor_get(v_l_729_, 4);
lean_inc(v_r_864_);
if (lean_obj_tag(v_r_864_) == 0)
{
lean_object* v_k_865_; lean_object* v_v_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_888_; 
lean_inc(v_l_819_);
v_k_865_ = lean_ctor_get(v_l_729_, 1);
v_v_866_ = lean_ctor_get(v_l_729_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_l_729_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; 
v_unused_889_ = lean_ctor_get(v_l_729_, 4);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_l_729_, 3);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_l_729_, 0);
lean_dec(v_unused_891_);
v___x_868_ = v_l_729_;
v_isShared_869_ = v_isSharedCheck_888_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_v_866_);
lean_inc(v_k_865_);
lean_dec(v_l_729_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_888_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_k_870_; lean_object* v_v_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_884_; 
v_k_870_ = lean_ctor_get(v_r_864_, 1);
v_v_871_ = lean_ctor_get(v_r_864_, 2);
v_isSharedCheck_884_ = !lean_is_exclusive(v_r_864_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_885_ = lean_ctor_get(v_r_864_, 4);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_r_864_, 3);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_r_864_, 0);
lean_dec(v_unused_887_);
v___x_873_ = v_r_864_;
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_v_871_);
lean_inc(v_k_870_);
lean_dec(v_r_864_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = lean_unsigned_to_nat(3u);
v___x_876_ = lean_unsigned_to_nat(1u);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 4, v_l_819_);
lean_ctor_set(v___x_873_, 3, v_l_819_);
lean_ctor_set(v___x_873_, 2, v_v_866_);
lean_ctor_set(v___x_873_, 1, v_k_865_);
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_k_865_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_v_866_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_l_819_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v_l_819_);
v___x_878_ = v_reuseFailAlloc_883_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 4, v_l_819_);
lean_ctor_set(v___x_868_, 2, v_v_728_);
lean_ctor_set(v___x_868_, 1, v_k_727_);
lean_ctor_set(v___x_868_, 0, v___x_876_);
v___x_880_ = v___x_868_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_l_819_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_l_819_);
v___x_880_ = v_reuseFailAlloc_882_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_881_, 0, v___x_875_);
lean_ctor_set(v___x_881_, 1, v_k_870_);
lean_ctor_set(v___x_881_, 2, v_v_871_);
lean_ctor_set(v___x_881_, 3, v___x_878_);
lean_ctor_set(v___x_881_, 4, v___x_880_);
return v___x_881_;
}
}
}
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(2u);
v___x_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_k_727_);
lean_ctor_set(v___x_893_, 2, v_v_728_);
lean_ctor_set(v___x_893_, 3, v_l_729_);
lean_ctor_set(v___x_893_, 4, v_r_864_);
return v___x_893_;
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v_k_727_);
lean_ctor_set(v___x_895_, 2, v_v_728_);
lean_ctor_set(v___x_895_, 3, v_l_729_);
lean_ctor_set(v___x_895_, 4, v_l_729_);
return v___x_895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceLErase(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_k_898_, lean_object* v_v_899_, lean_object* v_l_900_, lean_object* v_r_901_, lean_object* v_hlb_902_, lean_object* v_hrb_903_, lean_object* v_hlr_904_){
_start:
{
if (lean_obj_tag(v_r_901_) == 0)
{
if (lean_obj_tag(v_l_900_) == 0)
{
lean_object* v_size_905_; lean_object* v_size_906_; lean_object* v_k_907_; lean_object* v_v_908_; lean_object* v_l_909_; lean_object* v_r_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_size_905_ = lean_ctor_get(v_r_901_, 0);
v_size_906_ = lean_ctor_get(v_l_900_, 0);
v_k_907_ = lean_ctor_get(v_l_900_, 1);
v_v_908_ = lean_ctor_get(v_l_900_, 2);
v_l_909_ = lean_ctor_get(v_l_900_, 3);
v_r_910_ = lean_ctor_get(v_l_900_, 4);
lean_inc(v_r_910_);
v___x_911_ = lean_unsigned_to_nat(3u);
v___x_912_ = lean_nat_mul(v___x_911_, v_size_905_);
v___x_913_ = lean_nat_dec_lt(v___x_912_, v_size_906_);
lean_dec(v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v_r_910_);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_add(v___x_914_, v_size_906_);
v___x_916_ = lean_nat_add(v___x_915_, v_size_905_);
lean_dec(v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_k_898_);
lean_ctor_set(v___x_917_, 2, v_v_899_);
lean_ctor_set(v___x_917_, 3, v_l_900_);
lean_ctor_set(v___x_917_, 4, v_r_901_);
return v___x_917_;
}
else
{
lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_l_909_);
lean_inc(v_v_908_);
lean_inc(v_k_907_);
lean_inc(v_size_906_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_l_900_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; 
v_unused_984_ = lean_ctor_get(v_l_900_, 4);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_l_900_, 3);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_l_900_, 2);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_900_, 1);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_900_, 0);
lean_dec(v_unused_988_);
v___x_919_ = v_l_900_;
v_isShared_920_ = v_isSharedCheck_983_;
goto v_resetjp_918_;
}
else
{
lean_dec(v_l_900_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_983_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_size_921_; lean_object* v_size_922_; lean_object* v_k_923_; lean_object* v_v_924_; lean_object* v_l_925_; lean_object* v_r_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_size_921_ = lean_ctor_get(v_l_909_, 0);
v_size_922_ = lean_ctor_get(v_r_910_, 0);
v_k_923_ = lean_ctor_get(v_r_910_, 1);
v_v_924_ = lean_ctor_get(v_r_910_, 2);
v_l_925_ = lean_ctor_get(v_r_910_, 3);
v_r_926_ = lean_ctor_get(v_r_910_, 4);
v___x_927_ = lean_unsigned_to_nat(2u);
v___x_928_ = lean_nat_mul(v___x_927_, v_size_921_);
v___x_929_ = lean_nat_dec_lt(v_size_922_, v___x_928_);
lean_dec(v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_957_; 
lean_inc(v_r_926_);
lean_inc(v_l_925_);
lean_inc(v_v_924_);
lean_inc(v_k_923_);
v_isSharedCheck_957_ = !lean_is_exclusive(v_r_910_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; 
v_unused_958_ = lean_ctor_get(v_r_910_, 4);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_r_910_, 3);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_r_910_, 2);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_r_910_, 1);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_r_910_, 0);
lean_dec(v_unused_962_);
v___x_931_ = v_r_910_;
v_isShared_932_ = v_isSharedCheck_957_;
goto v_resetjp_930_;
}
else
{
lean_dec(v_r_910_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_957_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___x_947_; lean_object* v___y_949_; 
v___x_933_ = lean_unsigned_to_nat(1u);
v___x_934_ = lean_nat_add(v___x_933_, v_size_906_);
lean_dec(v_size_906_);
v___x_935_ = lean_nat_add(v___x_934_, v_size_905_);
lean_dec(v___x_934_);
v___x_947_ = lean_nat_add(v___x_933_, v_size_921_);
if (lean_obj_tag(v_l_925_) == 0)
{
lean_object* v_size_955_; 
v_size_955_ = lean_ctor_get(v_l_925_, 0);
lean_inc(v_size_955_);
v___y_949_ = v_size_955_;
goto v___jp_948_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___y_949_ = v___x_956_;
goto v___jp_948_;
}
v___jp_936_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = lean_nat_add(v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v_r_901_);
lean_ctor_set(v___x_931_, 3, v_r_926_);
lean_ctor_set(v___x_931_, 2, v_v_899_);
lean_ctor_set(v___x_931_, 1, v_k_898_);
lean_ctor_set(v___x_931_, 0, v___x_940_);
v___x_942_ = v___x_931_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_r_926_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_r_901_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v___x_942_);
lean_ctor_set(v___x_919_, 3, v___y_937_);
lean_ctor_set(v___x_919_, 2, v_v_924_);
lean_ctor_set(v___x_919_, 1, v_k_923_);
lean_ctor_set(v___x_919_, 0, v___x_935_);
v___x_944_ = v___x_919_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_923_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_924_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v___y_937_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_nat_add(v___x_947_, v___y_949_);
lean_dec(v___y_949_);
lean_dec(v___x_947_);
v___x_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v_k_907_);
lean_ctor_set(v___x_951_, 2, v_v_908_);
lean_ctor_set(v___x_951_, 3, v_l_909_);
lean_ctor_set(v___x_951_, 4, v_l_925_);
v___x_952_ = lean_nat_add(v___x_933_, v_size_905_);
if (lean_obj_tag(v_r_926_) == 0)
{
lean_object* v_size_953_; 
v_size_953_ = lean_ctor_get(v_r_926_, 0);
lean_inc(v_size_953_);
v___y_937_ = v___x_951_;
v___y_938_ = v___x_952_;
v___y_939_ = v_size_953_;
goto v___jp_936_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___y_937_ = v___x_951_;
v___y_938_ = v___x_952_;
v___y_939_ = v___x_954_;
goto v___jp_936_;
}
}
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_nat_add(v___x_963_, v_size_906_);
lean_dec(v_size_906_);
v___x_965_ = lean_nat_add(v___x_964_, v_size_905_);
lean_dec(v___x_964_);
v___x_966_ = lean_nat_add(v___x_963_, v_size_905_);
v___x_967_ = lean_nat_add(v___x_966_, v_size_922_);
lean_dec(v___x_966_);
lean_inc_ref(v_r_901_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_r_901_);
lean_ctor_set(v___x_919_, 3, v_r_910_);
lean_ctor_set(v___x_919_, 2, v_v_899_);
lean_ctor_set(v___x_919_, 1, v_k_898_);
lean_ctor_set(v___x_919_, 0, v___x_967_);
v___x_969_ = v___x_919_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_r_910_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_r_901_);
v___x_969_ = v_reuseFailAlloc_982_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v_r_901_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_977_ = lean_ctor_get(v_r_901_, 4);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_r_901_, 3);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_r_901_, 2);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_r_901_, 1);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_r_901_, 0);
lean_dec(v_unused_981_);
v___x_971_ = v_r_901_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_dec(v_r_901_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 4, v___x_969_);
lean_ctor_set(v___x_971_, 3, v_l_909_);
lean_ctor_set(v___x_971_, 2, v_v_908_);
lean_ctor_set(v___x_971_, 1, v_k_907_);
lean_ctor_set(v___x_971_, 0, v___x_965_);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_907_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_908_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_l_909_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v___x_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_size_989_ = lean_ctor_get(v_r_901_, 0);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v___x_990_, v_size_989_);
v___x_992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v_k_898_);
lean_ctor_set(v___x_992_, 2, v_v_899_);
lean_ctor_set(v___x_992_, 3, v_l_900_);
lean_ctor_set(v___x_992_, 4, v_r_901_);
return v___x_992_;
}
}
else
{
if (lean_obj_tag(v_l_900_) == 0)
{
lean_object* v_l_993_; 
v_l_993_ = lean_ctor_get(v_l_900_, 3);
if (lean_obj_tag(v_l_993_) == 0)
{
lean_object* v_r_994_; 
lean_inc_ref(v_l_993_);
v_r_994_ = lean_ctor_get(v_l_900_, 4);
lean_inc(v_r_994_);
if (lean_obj_tag(v_r_994_) == 0)
{
lean_object* v_size_995_; lean_object* v_k_996_; lean_object* v_v_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1020_; 
v_size_995_ = lean_ctor_get(v_l_900_, 0);
v_k_996_ = lean_ctor_get(v_l_900_, 1);
v_v_997_ = lean_ctor_get(v_l_900_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_l_900_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; 
v_unused_1021_ = lean_ctor_get(v_l_900_, 4);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_l_900_, 3);
lean_dec(v_unused_1022_);
v___x_999_ = v_l_900_;
v_isShared_1000_ = v_isSharedCheck_1020_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_v_997_);
lean_inc(v_k_996_);
lean_inc(v_size_995_);
lean_dec(v_l_900_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1020_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_size_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v_size_1001_ = lean_ctor_get(v_r_994_, 0);
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v___x_1002_, v_size_995_);
lean_dec(v_size_995_);
v___x_1004_ = lean_nat_add(v___x_1002_, v_size_1001_);
lean_inc_ref(v_r_994_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 4, v_r_901_);
lean_ctor_set(v___x_999_, 3, v_r_994_);
lean_ctor_set(v___x_999_, 2, v_v_899_);
lean_ctor_set(v___x_999_, 1, v_k_898_);
lean_ctor_set(v___x_999_, 0, v___x_1004_);
v___x_1006_ = v___x_999_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_r_994_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_r_901_);
v___x_1006_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_isSharedCheck_1013_ = !lean_is_exclusive(v_r_994_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1014_ = lean_ctor_get(v_r_994_, 4);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_r_994_, 3);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_r_994_, 2);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_r_994_, 1);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_994_, 0);
lean_dec(v_unused_1018_);
v___x_1008_ = v_r_994_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_dec(v_r_994_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v___x_1006_);
lean_ctor_set(v___x_1008_, 3, v_l_993_);
lean_ctor_set(v___x_1008_, 2, v_v_997_);
lean_ctor_set(v___x_1008_, 1, v_k_996_);
lean_ctor_set(v___x_1008_, 0, v___x_1003_);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_k_996_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_v_997_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_l_993_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v___x_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
else
{
lean_object* v_k_1023_; lean_object* v_v_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1034_; 
v_k_1023_ = lean_ctor_get(v_l_900_, 1);
v_v_1024_ = lean_ctor_get(v_l_900_, 2);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_l_900_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; lean_object* v_unused_1036_; lean_object* v_unused_1037_; 
v_unused_1035_ = lean_ctor_get(v_l_900_, 4);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_l_900_, 3);
lean_dec(v_unused_1036_);
v_unused_1037_ = lean_ctor_get(v_l_900_, 0);
lean_dec(v_unused_1037_);
v___x_1026_ = v_l_900_;
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_v_1024_);
lean_inc(v_k_1023_);
lean_dec(v_l_900_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1028_ = lean_unsigned_to_nat(3u);
v___x_1029_ = lean_unsigned_to_nat(1u);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 3, v_r_994_);
lean_ctor_set(v___x_1026_, 2, v_v_899_);
lean_ctor_set(v___x_1026_, 1, v_k_898_);
lean_ctor_set(v___x_1026_, 0, v___x_1029_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_r_994_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_r_994_);
v___x_1031_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1028_);
lean_ctor_set(v___x_1032_, 1, v_k_1023_);
lean_ctor_set(v___x_1032_, 2, v_v_1024_);
lean_ctor_set(v___x_1032_, 3, v_l_993_);
lean_ctor_set(v___x_1032_, 4, v___x_1031_);
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_r_1038_; 
v_r_1038_ = lean_ctor_get(v_l_900_, 4);
lean_inc(v_r_1038_);
if (lean_obj_tag(v_r_1038_) == 0)
{
lean_object* v_k_1039_; lean_object* v_v_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1062_; 
lean_inc(v_l_993_);
v_k_1039_ = lean_ctor_get(v_l_900_, 1);
v_v_1040_ = lean_ctor_get(v_l_900_, 2);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_l_900_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; lean_object* v_unused_1064_; lean_object* v_unused_1065_; 
v_unused_1063_ = lean_ctor_get(v_l_900_, 4);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_l_900_, 3);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_l_900_, 0);
lean_dec(v_unused_1065_);
v___x_1042_ = v_l_900_;
v_isShared_1043_ = v_isSharedCheck_1062_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_v_1040_);
lean_inc(v_k_1039_);
lean_dec(v_l_900_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1062_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_k_1044_; lean_object* v_v_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1058_; 
v_k_1044_ = lean_ctor_get(v_r_1038_, 1);
v_v_1045_ = lean_ctor_get(v_r_1038_, 2);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_r_1038_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; 
v_unused_1059_ = lean_ctor_get(v_r_1038_, 4);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_r_1038_, 3);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_r_1038_, 0);
lean_dec(v_unused_1061_);
v___x_1047_ = v_r_1038_;
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_v_1045_);
lean_inc(v_k_1044_);
lean_dec(v_r_1038_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = lean_unsigned_to_nat(3u);
v___x_1050_ = lean_unsigned_to_nat(1u);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_l_993_);
lean_ctor_set(v___x_1047_, 3, v_l_993_);
lean_ctor_set(v___x_1047_, 2, v_v_1040_);
lean_ctor_set(v___x_1047_, 1, v_k_1039_);
lean_ctor_set(v___x_1047_, 0, v___x_1050_);
v___x_1052_ = v___x_1047_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_l_993_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v_l_993_);
v___x_1052_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v_l_993_);
lean_ctor_set(v___x_1042_, 2, v_v_899_);
lean_ctor_set(v___x_1042_, 1, v_k_898_);
lean_ctor_set(v___x_1042_, 0, v___x_1050_);
v___x_1054_ = v___x_1042_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_l_993_);
lean_ctor_set(v_reuseFailAlloc_1056_, 4, v_l_993_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1049_);
lean_ctor_set(v___x_1055_, 1, v_k_1044_);
lean_ctor_set(v___x_1055_, 2, v_v_1045_);
lean_ctor_set(v___x_1055_, 3, v___x_1052_);
lean_ctor_set(v___x_1055_, 4, v___x_1054_);
return v___x_1055_;
}
}
}
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(2u);
v___x_1067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_k_898_);
lean_ctor_set(v___x_1067_, 2, v_v_899_);
lean_ctor_set(v___x_1067_, 3, v_l_900_);
lean_ctor_set(v___x_1067_, 4, v_r_1038_);
return v___x_1067_;
}
}
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_k_898_);
lean_ctor_set(v___x_1069_, 2, v_v_899_);
lean_ctor_set(v___x_1069_, 3, v_l_900_);
lean_ctor_set(v___x_1069_, 4, v_l_900_);
return v___x_1069_;
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1073_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2));
v___x_1074_ = lean_unsigned_to_nat(35u);
v___x_1075_ = lean_unsigned_to_nat(182u);
v___x_1076_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1));
v___x_1077_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_1078_ = l_mkPanicMessageWithDecl(v___x_1077_, v___x_1076_, v___x_1075_, v___x_1074_, v___x_1073_);
return v___x_1078_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1079_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__2));
v___x_1080_ = lean_unsigned_to_nat(21u);
v___x_1081_ = lean_unsigned_to_nat(183u);
v___x_1082_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__1));
v___x_1083_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_1084_ = l_mkPanicMessageWithDecl(v___x_1083_, v___x_1082_, v___x_1081_, v___x_1080_, v___x_1079_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg(lean_object* v_k_1085_, lean_object* v_v_1086_, lean_object* v_l_1087_, lean_object* v_r_1088_){
_start:
{
if (lean_obj_tag(v_r_1088_) == 0)
{
if (lean_obj_tag(v_l_1087_) == 0)
{
lean_object* v_size_1089_; lean_object* v_size_1090_; lean_object* v_k_1091_; lean_object* v_v_1092_; lean_object* v_l_1093_; lean_object* v_r_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_size_1089_ = lean_ctor_get(v_r_1088_, 0);
v_size_1090_ = lean_ctor_get(v_l_1087_, 0);
v_k_1091_ = lean_ctor_get(v_l_1087_, 1);
v_v_1092_ = lean_ctor_get(v_l_1087_, 2);
v_l_1093_ = lean_ctor_get(v_l_1087_, 3);
v_r_1094_ = lean_ctor_get(v_l_1087_, 4);
lean_inc(v_r_1094_);
v___x_1095_ = lean_unsigned_to_nat(3u);
v___x_1096_ = lean_nat_mul(v___x_1095_, v_size_1089_);
v___x_1097_ = lean_nat_dec_lt(v___x_1096_, v_size_1090_);
lean_dec(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_r_1094_);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_add(v___x_1098_, v_size_1090_);
v___x_1100_ = lean_nat_add(v___x_1099_, v_size_1089_);
lean_dec(v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_k_1085_);
lean_ctor_set(v___x_1101_, 2, v_v_1086_);
lean_ctor_set(v___x_1101_, 3, v_l_1087_);
lean_ctor_set(v___x_1101_, 4, v_r_1088_);
return v___x_1101_;
}
else
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1173_; 
lean_inc(v_l_1093_);
lean_inc(v_v_1092_);
lean_inc(v_k_1091_);
lean_inc(v_size_1090_);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1174_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_l_1087_, 2);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_l_1087_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_l_1087_, 0);
lean_dec(v_unused_1178_);
v___x_1103_ = v_l_1087_;
v_isShared_1104_ = v_isSharedCheck_1173_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_l_1087_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1173_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
if (lean_obj_tag(v_l_1093_) == 0)
{
if (lean_obj_tag(v_r_1094_) == 0)
{
lean_object* v_size_1105_; lean_object* v_size_1106_; lean_object* v_k_1107_; lean_object* v_v_1108_; lean_object* v_l_1109_; lean_object* v_r_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_size_1105_ = lean_ctor_get(v_l_1093_, 0);
v_size_1106_ = lean_ctor_get(v_r_1094_, 0);
v_k_1107_ = lean_ctor_get(v_r_1094_, 1);
v_v_1108_ = lean_ctor_get(v_r_1094_, 2);
v_l_1109_ = lean_ctor_get(v_r_1094_, 3);
v_r_1110_ = lean_ctor_get(v_r_1094_, 4);
v___x_1111_ = lean_unsigned_to_nat(2u);
v___x_1112_ = lean_nat_mul(v___x_1111_, v_size_1105_);
v___x_1113_ = lean_nat_dec_lt(v_size_1106_, v___x_1112_);
lean_dec(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1141_; 
lean_inc(v_r_1110_);
lean_inc(v_l_1109_);
lean_inc(v_v_1108_);
lean_inc(v_k_1107_);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_r_1094_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; lean_object* v_unused_1146_; 
v_unused_1142_ = lean_ctor_get(v_r_1094_, 4);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_r_1094_, 3);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_r_1094_, 2);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_r_1094_, 1);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_r_1094_, 0);
lean_dec(v_unused_1146_);
v___x_1115_ = v_r_1094_;
v_isShared_1116_ = v_isSharedCheck_1141_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v_r_1094_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1141_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___x_1131_; lean_object* v___y_1133_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v___x_1117_, v_size_1090_);
lean_dec(v_size_1090_);
v___x_1119_ = lean_nat_add(v___x_1118_, v_size_1089_);
lean_dec(v___x_1118_);
v___x_1131_ = lean_nat_add(v___x_1117_, v_size_1105_);
if (lean_obj_tag(v_l_1109_) == 0)
{
lean_object* v_size_1139_; 
v_size_1139_ = lean_ctor_get(v_l_1109_, 0);
lean_inc(v_size_1139_);
v___y_1133_ = v_size_1139_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_unsigned_to_nat(0u);
v___y_1133_ = v___x_1140_;
goto v___jp_1132_;
}
v___jp_1120_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_nat_add(v___y_1121_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec(v___y_1121_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 4, v_r_1088_);
lean_ctor_set(v___x_1115_, 3, v_r_1110_);
lean_ctor_set(v___x_1115_, 2, v_v_1086_);
lean_ctor_set(v___x_1115_, 1, v_k_1085_);
lean_ctor_set(v___x_1115_, 0, v___x_1124_);
v___x_1126_ = v___x_1115_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_r_1110_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_r_1088_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v___x_1126_);
lean_ctor_set(v___x_1103_, 3, v___y_1122_);
lean_ctor_set(v___x_1103_, 2, v_v_1108_);
lean_ctor_set(v___x_1103_, 1, v_k_1107_);
lean_ctor_set(v___x_1103_, 0, v___x_1119_);
v___x_1128_ = v___x_1103_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_k_1107_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_v_1108_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v___y_1122_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
v___jp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_nat_add(v___x_1131_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_k_1091_);
lean_ctor_set(v___x_1135_, 2, v_v_1092_);
lean_ctor_set(v___x_1135_, 3, v_l_1093_);
lean_ctor_set(v___x_1135_, 4, v_l_1109_);
v___x_1136_ = lean_nat_add(v___x_1117_, v_size_1089_);
if (lean_obj_tag(v_r_1110_) == 0)
{
lean_object* v_size_1137_; 
v_size_1137_ = lean_ctor_get(v_r_1110_, 0);
lean_inc(v_size_1137_);
v___y_1121_ = v___x_1136_;
v___y_1122_ = v___x_1135_;
v___y_1123_ = v_size_1137_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___y_1121_ = v___x_1136_;
v___y_1122_ = v___x_1135_;
v___y_1123_ = v___x_1138_;
goto v___jp_1120_;
}
}
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_nat_add(v___x_1147_, v_size_1090_);
lean_dec(v_size_1090_);
v___x_1149_ = lean_nat_add(v___x_1148_, v_size_1089_);
lean_dec(v___x_1148_);
v___x_1150_ = lean_nat_add(v___x_1147_, v_size_1089_);
v___x_1151_ = lean_nat_add(v___x_1150_, v_size_1106_);
lean_dec(v___x_1150_);
lean_inc_ref(v_r_1088_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_r_1088_);
lean_ctor_set(v___x_1103_, 3, v_r_1094_);
lean_ctor_set(v___x_1103_, 2, v_v_1086_);
lean_ctor_set(v___x_1103_, 1, v_k_1085_);
lean_ctor_set(v___x_1103_, 0, v___x_1151_);
v___x_1153_ = v___x_1103_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_r_1094_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_r_1088_);
v___x_1153_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_isSharedCheck_1160_ = !lean_is_exclusive(v_r_1088_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1161_ = lean_ctor_get(v_r_1088_, 4);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_r_1088_, 3);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_r_1088_, 2);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_r_1088_, 1);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_r_1088_, 0);
lean_dec(v_unused_1165_);
v___x_1155_ = v_r_1088_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_dec(v_r_1088_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 4, v___x_1153_);
lean_ctor_set(v___x_1155_, 3, v_l_1093_);
lean_ctor_set(v___x_1155_, 2, v_v_1092_);
lean_ctor_set(v___x_1155_, 1, v_k_1091_);
lean_ctor_set(v___x_1155_, 0, v___x_1149_);
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_l_1093_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v___x_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec_ref(v_l_1093_);
lean_del_object(v___x_1103_);
lean_dec(v_v_1092_);
lean_dec(v_k_1091_);
lean_dec(v_size_1090_);
lean_dec_ref(v_r_1088_);
lean_dec(v_v_1086_);
lean_dec(v_k_1085_);
v___x_1167_ = lean_box(1);
v___x_1168_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
v___x_1169_ = l_panic___redArg(v___x_1167_, v___x_1168_);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_del_object(v___x_1103_);
lean_dec(v_r_1094_);
lean_dec(v_v_1092_);
lean_dec(v_k_1091_);
lean_dec(v_size_1090_);
lean_dec_ref(v_r_1088_);
lean_dec(v_v_1086_);
lean_dec(v_k_1085_);
v___x_1170_ = lean_box(1);
v___x_1171_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
v___x_1172_ = l_panic___redArg(v___x_1170_, v___x_1171_);
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_size_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_size_1179_ = lean_ctor_get(v_r_1088_, 0);
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_nat_add(v___x_1180_, v_size_1179_);
v___x_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v_k_1085_);
lean_ctor_set(v___x_1182_, 2, v_v_1086_);
lean_ctor_set(v___x_1182_, 3, v_l_1087_);
lean_ctor_set(v___x_1182_, 4, v_r_1088_);
return v___x_1182_;
}
}
else
{
if (lean_obj_tag(v_l_1087_) == 0)
{
lean_object* v_l_1183_; 
v_l_1183_ = lean_ctor_get(v_l_1087_, 3);
if (lean_obj_tag(v_l_1183_) == 0)
{
lean_object* v_r_1184_; 
lean_inc_ref(v_l_1183_);
v_r_1184_ = lean_ctor_get(v_l_1087_, 4);
lean_inc(v_r_1184_);
if (lean_obj_tag(v_r_1184_) == 0)
{
lean_object* v_size_1185_; lean_object* v_k_1186_; lean_object* v_v_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1210_; 
v_size_1185_ = lean_ctor_get(v_l_1087_, 0);
v_k_1186_ = lean_ctor_get(v_l_1087_, 1);
v_v_1187_ = lean_ctor_get(v_l_1087_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1211_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1212_);
v___x_1189_ = v_l_1087_;
v_isShared_1190_ = v_isSharedCheck_1210_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_v_1187_);
lean_inc(v_k_1186_);
lean_inc(v_size_1185_);
lean_dec(v_l_1087_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1210_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_size_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v_size_1191_ = lean_ctor_get(v_r_1184_, 0);
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_add(v___x_1192_, v_size_1185_);
lean_dec(v_size_1185_);
v___x_1194_ = lean_nat_add(v___x_1192_, v_size_1191_);
lean_inc_ref(v_r_1184_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 4, v_r_1088_);
lean_ctor_set(v___x_1189_, 3, v_r_1184_);
lean_ctor_set(v___x_1189_, 2, v_v_1086_);
lean_ctor_set(v___x_1189_, 1, v_k_1085_);
lean_ctor_set(v___x_1189_, 0, v___x_1194_);
v___x_1196_ = v___x_1189_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_r_1184_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_r_1088_);
v___x_1196_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_isSharedCheck_1203_ = !lean_is_exclusive(v_r_1184_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; lean_object* v_unused_1205_; lean_object* v_unused_1206_; lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1204_ = lean_ctor_get(v_r_1184_, 4);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_r_1184_, 3);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_r_1184_, 2);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_r_1184_, 1);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_r_1184_, 0);
lean_dec(v_unused_1208_);
v___x_1198_ = v_r_1184_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_dec(v_r_1184_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 4, v___x_1196_);
lean_ctor_set(v___x_1198_, 3, v_l_1183_);
lean_ctor_set(v___x_1198_, 2, v_v_1187_);
lean_ctor_set(v___x_1198_, 1, v_k_1186_);
lean_ctor_set(v___x_1198_, 0, v___x_1193_);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_k_1186_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_v_1187_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_l_1183_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v___x_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
else
{
lean_object* v_k_1213_; lean_object* v_v_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1224_; 
v_k_1213_ = lean_ctor_get(v_l_1087_, 1);
v_v_1214_ = lean_ctor_get(v_l_1087_, 2);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1225_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_l_1087_, 0);
lean_dec(v_unused_1227_);
v___x_1216_ = v_l_1087_;
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_v_1214_);
lean_inc(v_k_1213_);
lean_dec(v_l_1087_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1218_ = lean_unsigned_to_nat(3u);
v___x_1219_ = lean_unsigned_to_nat(1u);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 3, v_r_1184_);
lean_ctor_set(v___x_1216_, 2, v_v_1086_);
lean_ctor_set(v___x_1216_, 1, v_k_1085_);
lean_ctor_set(v___x_1216_, 0, v___x_1219_);
v___x_1221_ = v___x_1216_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_r_1184_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_r_1184_);
v___x_1221_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1218_);
lean_ctor_set(v___x_1222_, 1, v_k_1213_);
lean_ctor_set(v___x_1222_, 2, v_v_1214_);
lean_ctor_set(v___x_1222_, 3, v_l_1183_);
lean_ctor_set(v___x_1222_, 4, v___x_1221_);
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_r_1228_; 
v_r_1228_ = lean_ctor_get(v_l_1087_, 4);
lean_inc(v_r_1228_);
if (lean_obj_tag(v_r_1228_) == 0)
{
lean_object* v_k_1229_; lean_object* v_v_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1252_; 
lean_inc(v_l_1183_);
v_k_1229_ = lean_ctor_get(v_l_1087_, 1);
v_v_1230_ = lean_ctor_get(v_l_1087_, 2);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; lean_object* v_unused_1254_; lean_object* v_unused_1255_; 
v_unused_1253_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_l_1087_, 0);
lean_dec(v_unused_1255_);
v___x_1232_ = v_l_1087_;
v_isShared_1233_ = v_isSharedCheck_1252_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_v_1230_);
lean_inc(v_k_1229_);
lean_dec(v_l_1087_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1252_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_k_1234_; lean_object* v_v_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1248_; 
v_k_1234_ = lean_ctor_get(v_r_1228_, 1);
v_v_1235_ = lean_ctor_get(v_r_1228_, 2);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_r_1228_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; lean_object* v_unused_1250_; lean_object* v_unused_1251_; 
v_unused_1249_ = lean_ctor_get(v_r_1228_, 4);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v_r_1228_, 3);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_r_1228_, 0);
lean_dec(v_unused_1251_);
v___x_1237_ = v_r_1228_;
v_isShared_1238_ = v_isSharedCheck_1248_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_v_1235_);
lean_inc(v_k_1234_);
lean_dec(v_r_1228_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1248_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1239_ = lean_unsigned_to_nat(3u);
v___x_1240_ = lean_unsigned_to_nat(1u);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 4, v_l_1183_);
lean_ctor_set(v___x_1237_, 3, v_l_1183_);
lean_ctor_set(v___x_1237_, 2, v_v_1230_);
lean_ctor_set(v___x_1237_, 1, v_k_1229_);
lean_ctor_set(v___x_1237_, 0, v___x_1240_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_1229_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_1230_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_l_1183_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_l_1183_);
v___x_1242_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 4, v_l_1183_);
lean_ctor_set(v___x_1232_, 2, v_v_1086_);
lean_ctor_set(v___x_1232_, 1, v_k_1085_);
lean_ctor_set(v___x_1232_, 0, v___x_1240_);
v___x_1244_ = v___x_1232_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_l_1183_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_l_1183_);
v___x_1244_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1239_);
lean_ctor_set(v___x_1245_, 1, v_k_1234_);
lean_ctor_set(v___x_1245_, 2, v_v_1235_);
lean_ctor_set(v___x_1245_, 3, v___x_1242_);
lean_ctor_set(v___x_1245_, 4, v___x_1244_);
return v___x_1245_;
}
}
}
}
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_unsigned_to_nat(2u);
v___x_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_k_1085_);
lean_ctor_set(v___x_1257_, 2, v_v_1086_);
lean_ctor_set(v___x_1257_, 3, v_l_1087_);
lean_ctor_set(v___x_1257_, 4, v_r_1228_);
return v___x_1257_;
}
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_k_1085_);
lean_ctor_set(v___x_1259_, 2, v_v_1086_);
lean_ctor_set(v___x_1259_, 3, v_l_1087_);
lean_ctor_set(v___x_1259_, 4, v_l_1087_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_k_1262_, lean_object* v_v_1263_, lean_object* v_l_1264_, lean_object* v_r_1265_){
_start:
{
if (lean_obj_tag(v_r_1265_) == 0)
{
if (lean_obj_tag(v_l_1264_) == 0)
{
lean_object* v_size_1266_; lean_object* v_size_1267_; lean_object* v_k_1268_; lean_object* v_v_1269_; lean_object* v_l_1270_; lean_object* v_r_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v_size_1266_ = lean_ctor_get(v_r_1265_, 0);
v_size_1267_ = lean_ctor_get(v_l_1264_, 0);
v_k_1268_ = lean_ctor_get(v_l_1264_, 1);
v_v_1269_ = lean_ctor_get(v_l_1264_, 2);
v_l_1270_ = lean_ctor_get(v_l_1264_, 3);
v_r_1271_ = lean_ctor_get(v_l_1264_, 4);
lean_inc(v_r_1271_);
v___x_1272_ = lean_unsigned_to_nat(3u);
v___x_1273_ = lean_nat_mul(v___x_1272_, v_size_1266_);
v___x_1274_ = lean_nat_dec_lt(v___x_1273_, v_size_1267_);
lean_dec(v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_r_1271_);
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v___x_1275_, v_size_1267_);
v___x_1277_ = lean_nat_add(v___x_1276_, v_size_1266_);
lean_dec(v___x_1276_);
v___x_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v_k_1262_);
lean_ctor_set(v___x_1278_, 2, v_v_1263_);
lean_ctor_set(v___x_1278_, 3, v_l_1264_);
lean_ctor_set(v___x_1278_, 4, v_r_1265_);
return v___x_1278_;
}
else
{
lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1350_; 
lean_inc(v_l_1270_);
lean_inc(v_v_1269_);
lean_inc(v_k_1268_);
lean_inc(v_size_1267_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_l_1264_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1351_ = lean_ctor_get(v_l_1264_, 4);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_l_1264_, 3);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_l_1264_, 2);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_l_1264_, 1);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_l_1264_, 0);
lean_dec(v_unused_1355_);
v___x_1280_ = v_l_1264_;
v_isShared_1281_ = v_isSharedCheck_1350_;
goto v_resetjp_1279_;
}
else
{
lean_dec(v_l_1264_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1350_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
if (lean_obj_tag(v_l_1270_) == 0)
{
if (lean_obj_tag(v_r_1271_) == 0)
{
lean_object* v_size_1282_; lean_object* v_size_1283_; lean_object* v_k_1284_; lean_object* v_v_1285_; lean_object* v_l_1286_; lean_object* v_r_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_size_1282_ = lean_ctor_get(v_l_1270_, 0);
v_size_1283_ = lean_ctor_get(v_r_1271_, 0);
v_k_1284_ = lean_ctor_get(v_r_1271_, 1);
v_v_1285_ = lean_ctor_get(v_r_1271_, 2);
v_l_1286_ = lean_ctor_get(v_r_1271_, 3);
v_r_1287_ = lean_ctor_get(v_r_1271_, 4);
v___x_1288_ = lean_unsigned_to_nat(2u);
v___x_1289_ = lean_nat_mul(v___x_1288_, v_size_1282_);
v___x_1290_ = lean_nat_dec_lt(v_size_1283_, v___x_1289_);
lean_dec(v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1318_; 
lean_inc(v_r_1287_);
lean_inc(v_l_1286_);
lean_inc(v_v_1285_);
lean_inc(v_k_1284_);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_r_1271_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; 
v_unused_1319_ = lean_ctor_get(v_r_1271_, 4);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_r_1271_, 3);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_r_1271_, 2);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_r_1271_, 1);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_r_1271_, 0);
lean_dec(v_unused_1323_);
v___x_1292_ = v_r_1271_;
v_isShared_1293_ = v_isSharedCheck_1318_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v_r_1271_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1318_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___x_1308_; lean_object* v___y_1310_; 
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v___x_1294_, v_size_1267_);
lean_dec(v_size_1267_);
v___x_1296_ = lean_nat_add(v___x_1295_, v_size_1266_);
lean_dec(v___x_1295_);
v___x_1308_ = lean_nat_add(v___x_1294_, v_size_1282_);
if (lean_obj_tag(v_l_1286_) == 0)
{
lean_object* v_size_1316_; 
v_size_1316_ = lean_ctor_get(v_l_1286_, 0);
lean_inc(v_size_1316_);
v___y_1310_ = v_size_1316_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___y_1310_ = v___x_1317_;
goto v___jp_1309_;
}
v___jp_1297_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_nat_add(v___y_1298_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec(v___y_1298_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_r_1265_);
lean_ctor_set(v___x_1292_, 3, v_r_1287_);
lean_ctor_set(v___x_1292_, 2, v_v_1263_);
lean_ctor_set(v___x_1292_, 1, v_k_1262_);
lean_ctor_set(v___x_1292_, 0, v___x_1301_);
v___x_1303_ = v___x_1292_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_r_1287_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v_r_1265_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 4, v___x_1303_);
lean_ctor_set(v___x_1280_, 3, v___y_1299_);
lean_ctor_set(v___x_1280_, 2, v_v_1285_);
lean_ctor_set(v___x_1280_, 1, v_k_1284_);
lean_ctor_set(v___x_1280_, 0, v___x_1296_);
v___x_1305_ = v___x_1280_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_k_1284_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_v_1285_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v___y_1299_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
v___jp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_nat_add(v___x_1308_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec(v___x_1308_);
v___x_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v_k_1268_);
lean_ctor_set(v___x_1312_, 2, v_v_1269_);
lean_ctor_set(v___x_1312_, 3, v_l_1270_);
lean_ctor_set(v___x_1312_, 4, v_l_1286_);
v___x_1313_ = lean_nat_add(v___x_1294_, v_size_1266_);
if (lean_obj_tag(v_r_1287_) == 0)
{
lean_object* v_size_1314_; 
v_size_1314_ = lean_ctor_get(v_r_1287_, 0);
lean_inc(v_size_1314_);
v___y_1298_ = v___x_1313_;
v___y_1299_ = v___x_1312_;
v___y_1300_ = v_size_1314_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___y_1298_ = v___x_1313_;
v___y_1299_ = v___x_1312_;
v___y_1300_ = v___x_1315_;
goto v___jp_1297_;
}
}
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_nat_add(v___x_1324_, v_size_1267_);
lean_dec(v_size_1267_);
v___x_1326_ = lean_nat_add(v___x_1325_, v_size_1266_);
lean_dec(v___x_1325_);
v___x_1327_ = lean_nat_add(v___x_1324_, v_size_1266_);
v___x_1328_ = lean_nat_add(v___x_1327_, v_size_1283_);
lean_dec(v___x_1327_);
lean_inc_ref(v_r_1265_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 4, v_r_1265_);
lean_ctor_set(v___x_1280_, 3, v_r_1271_);
lean_ctor_set(v___x_1280_, 2, v_v_1263_);
lean_ctor_set(v___x_1280_, 1, v_k_1262_);
lean_ctor_set(v___x_1280_, 0, v___x_1328_);
v___x_1330_ = v___x_1280_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_r_1271_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_r_1265_);
v___x_1330_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_isSharedCheck_1337_ = !lean_is_exclusive(v_r_1265_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; lean_object* v_unused_1339_; lean_object* v_unused_1340_; lean_object* v_unused_1341_; lean_object* v_unused_1342_; 
v_unused_1338_ = lean_ctor_get(v_r_1265_, 4);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_r_1265_, 3);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_r_1265_, 2);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v_r_1265_, 1);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_r_1265_, 0);
lean_dec(v_unused_1342_);
v___x_1332_ = v_r_1265_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v_r_1265_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v___x_1330_);
lean_ctor_set(v___x_1332_, 3, v_l_1270_);
lean_ctor_set(v___x_1332_, 2, v_v_1269_);
lean_ctor_set(v___x_1332_, 1, v_k_1268_);
lean_ctor_set(v___x_1332_, 0, v___x_1326_);
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1268_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1269_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_l_1270_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v___x_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v_l_1270_);
lean_del_object(v___x_1280_);
lean_dec(v_v_1269_);
lean_dec(v_k_1268_);
lean_dec(v_size_1267_);
lean_dec_ref(v_r_1265_);
lean_dec(v_v_1263_);
lean_dec(v_k_1262_);
v___x_1344_ = lean_box(1);
v___x_1345_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
v___x_1346_ = l_panic___redArg(v___x_1344_, v___x_1345_);
return v___x_1346_;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1280_);
lean_dec(v_r_1271_);
lean_dec(v_v_1269_);
lean_dec(v_k_1268_);
lean_dec(v_size_1267_);
lean_dec_ref(v_r_1265_);
lean_dec(v_v_1263_);
lean_dec(v_k_1262_);
v___x_1347_ = lean_box(1);
v___x_1348_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
v___x_1349_ = l_panic___redArg(v___x_1347_, v___x_1348_);
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_size_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_size_1356_ = lean_ctor_get(v_r_1265_, 0);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_add(v___x_1357_, v_size_1356_);
v___x_1359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v_k_1262_);
lean_ctor_set(v___x_1359_, 2, v_v_1263_);
lean_ctor_set(v___x_1359_, 3, v_l_1264_);
lean_ctor_set(v___x_1359_, 4, v_r_1265_);
return v___x_1359_;
}
}
else
{
if (lean_obj_tag(v_l_1264_) == 0)
{
lean_object* v_l_1360_; 
v_l_1360_ = lean_ctor_get(v_l_1264_, 3);
if (lean_obj_tag(v_l_1360_) == 0)
{
lean_object* v_r_1361_; 
lean_inc_ref(v_l_1360_);
v_r_1361_ = lean_ctor_get(v_l_1264_, 4);
lean_inc(v_r_1361_);
if (lean_obj_tag(v_r_1361_) == 0)
{
lean_object* v_size_1362_; lean_object* v_k_1363_; lean_object* v_v_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1387_; 
v_size_1362_ = lean_ctor_get(v_l_1264_, 0);
v_k_1363_ = lean_ctor_get(v_l_1264_, 1);
v_v_1364_ = lean_ctor_get(v_l_1264_, 2);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_l_1264_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; lean_object* v_unused_1389_; 
v_unused_1388_ = lean_ctor_get(v_l_1264_, 4);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v_l_1264_, 3);
lean_dec(v_unused_1389_);
v___x_1366_ = v_l_1264_;
v_isShared_1367_ = v_isSharedCheck_1387_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_v_1364_);
lean_inc(v_k_1363_);
lean_inc(v_size_1362_);
lean_dec(v_l_1264_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1387_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_size_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v_size_1368_ = lean_ctor_get(v_r_1361_, 0);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v___x_1369_, v_size_1362_);
lean_dec(v_size_1362_);
v___x_1371_ = lean_nat_add(v___x_1369_, v_size_1368_);
lean_inc_ref(v_r_1361_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_r_1265_);
lean_ctor_set(v___x_1366_, 3, v_r_1361_);
lean_ctor_set(v___x_1366_, 2, v_v_1263_);
lean_ctor_set(v___x_1366_, 1, v_k_1262_);
lean_ctor_set(v___x_1366_, 0, v___x_1371_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_r_1361_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_r_1265_);
v___x_1373_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v_r_1361_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; lean_object* v_unused_1382_; lean_object* v_unused_1383_; lean_object* v_unused_1384_; lean_object* v_unused_1385_; 
v_unused_1381_ = lean_ctor_get(v_r_1361_, 4);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_r_1361_, 3);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_r_1361_, 2);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_r_1361_, 1);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_r_1361_, 0);
lean_dec(v_unused_1385_);
v___x_1375_ = v_r_1361_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v_r_1361_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1373_);
lean_ctor_set(v___x_1375_, 3, v_l_1360_);
lean_ctor_set(v___x_1375_, 2, v_v_1364_);
lean_ctor_set(v___x_1375_, 1, v_k_1363_);
lean_ctor_set(v___x_1375_, 0, v___x_1370_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_l_1360_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v___x_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
else
{
lean_object* v_k_1390_; lean_object* v_v_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1401_; 
v_k_1390_ = lean_ctor_get(v_l_1264_, 1);
v_v_1391_ = lean_ctor_get(v_l_1264_, 2);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_l_1264_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1402_ = lean_ctor_get(v_l_1264_, 4);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_l_1264_, 3);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_l_1264_, 0);
lean_dec(v_unused_1404_);
v___x_1393_ = v_l_1264_;
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_v_1391_);
lean_inc(v_k_1390_);
lean_dec(v_l_1264_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1395_ = lean_unsigned_to_nat(3u);
v___x_1396_ = lean_unsigned_to_nat(1u);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 3, v_r_1361_);
lean_ctor_set(v___x_1393_, 2, v_v_1263_);
lean_ctor_set(v___x_1393_, 1, v_k_1262_);
lean_ctor_set(v___x_1393_, 0, v___x_1396_);
v___x_1398_ = v___x_1393_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_r_1361_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_r_1361_);
v___x_1398_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1395_);
lean_ctor_set(v___x_1399_, 1, v_k_1390_);
lean_ctor_set(v___x_1399_, 2, v_v_1391_);
lean_ctor_set(v___x_1399_, 3, v_l_1360_);
lean_ctor_set(v___x_1399_, 4, v___x_1398_);
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_r_1405_; 
v_r_1405_ = lean_ctor_get(v_l_1264_, 4);
lean_inc(v_r_1405_);
if (lean_obj_tag(v_r_1405_) == 0)
{
lean_object* v_k_1406_; lean_object* v_v_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1429_; 
lean_inc(v_l_1360_);
v_k_1406_ = lean_ctor_get(v_l_1264_, 1);
v_v_1407_ = lean_ctor_get(v_l_1264_, 2);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_l_1264_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; 
v_unused_1430_ = lean_ctor_get(v_l_1264_, 4);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_l_1264_, 3);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_l_1264_, 0);
lean_dec(v_unused_1432_);
v___x_1409_ = v_l_1264_;
v_isShared_1410_ = v_isSharedCheck_1429_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_v_1407_);
lean_inc(v_k_1406_);
lean_dec(v_l_1264_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1429_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_k_1411_; lean_object* v_v_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1425_; 
v_k_1411_ = lean_ctor_get(v_r_1405_, 1);
v_v_1412_ = lean_ctor_get(v_r_1405_, 2);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_r_1405_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; 
v_unused_1426_ = lean_ctor_get(v_r_1405_, 4);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_r_1405_, 3);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_r_1405_, 0);
lean_dec(v_unused_1428_);
v___x_1414_ = v_r_1405_;
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_v_1412_);
lean_inc(v_k_1411_);
lean_dec(v_r_1405_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1416_ = lean_unsigned_to_nat(3u);
v___x_1417_ = lean_unsigned_to_nat(1u);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v_l_1360_);
lean_ctor_set(v___x_1414_, 3, v_l_1360_);
lean_ctor_set(v___x_1414_, 2, v_v_1407_);
lean_ctor_set(v___x_1414_, 1, v_k_1406_);
lean_ctor_set(v___x_1414_, 0, v___x_1417_);
v___x_1419_ = v___x_1414_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1407_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_l_1360_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_l_1360_);
v___x_1419_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1360_);
lean_ctor_set(v___x_1409_, 2, v_v_1263_);
lean_ctor_set(v___x_1409_, 1, v_k_1262_);
lean_ctor_set(v___x_1409_, 0, v___x_1417_);
v___x_1421_ = v___x_1409_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_l_1360_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_l_1360_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1416_);
lean_ctor_set(v___x_1422_, 1, v_k_1411_);
lean_ctor_set(v___x_1422_, 2, v_v_1412_);
lean_ctor_set(v___x_1422_, 3, v___x_1419_);
lean_ctor_set(v___x_1422_, 4, v___x_1421_);
return v___x_1422_;
}
}
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_unsigned_to_nat(2u);
v___x_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v_k_1262_);
lean_ctor_set(v___x_1434_, 2, v_v_1263_);
lean_ctor_set(v___x_1434_, 3, v_l_1264_);
lean_ctor_set(v___x_1434_, 4, v_r_1405_);
return v___x_1434_;
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_unsigned_to_nat(1u);
v___x_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v_k_1262_);
lean_ctor_set(v___x_1436_, 2, v_v_1263_);
lean_ctor_set(v___x_1436_, 3, v_l_1264_);
lean_ctor_set(v___x_1436_, 4, v_l_1264_);
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR___redArg(lean_object* v_k_1437_, lean_object* v_v_1438_, lean_object* v_l_1439_, lean_object* v_r_1440_){
_start:
{
if (lean_obj_tag(v_l_1439_) == 0)
{
if (lean_obj_tag(v_r_1440_) == 0)
{
lean_object* v_size_1441_; lean_object* v_size_1442_; lean_object* v_k_1443_; lean_object* v_v_1444_; lean_object* v_l_1445_; lean_object* v_r_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_size_1441_ = lean_ctor_get(v_l_1439_, 0);
v_size_1442_ = lean_ctor_get(v_r_1440_, 0);
v_k_1443_ = lean_ctor_get(v_r_1440_, 1);
v_v_1444_ = lean_ctor_get(v_r_1440_, 2);
v_l_1445_ = lean_ctor_get(v_r_1440_, 3);
lean_inc(v_l_1445_);
v_r_1446_ = lean_ctor_get(v_r_1440_, 4);
v___x_1447_ = lean_unsigned_to_nat(3u);
v___x_1448_ = lean_nat_mul(v___x_1447_, v_size_1441_);
v___x_1449_ = lean_nat_dec_lt(v___x_1448_, v_size_1442_);
lean_dec(v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec(v_l_1445_);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v___x_1450_, v_size_1441_);
v___x_1452_ = lean_nat_add(v___x_1451_, v_size_1442_);
lean_dec(v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v_k_1437_);
lean_ctor_set(v___x_1453_, 2, v_v_1438_);
lean_ctor_set(v___x_1453_, 3, v_l_1439_);
lean_ctor_set(v___x_1453_, 4, v_r_1440_);
return v___x_1453_;
}
else
{
lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1517_; 
lean_inc(v_r_1446_);
lean_inc(v_v_1444_);
lean_inc(v_k_1443_);
lean_inc(v_size_1442_);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_r_1440_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; 
v_unused_1518_ = lean_ctor_get(v_r_1440_, 4);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_r_1440_, 3);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1440_, 2);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1440_, 1);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1440_, 0);
lean_dec(v_unused_1522_);
v___x_1455_ = v_r_1440_;
v_isShared_1456_ = v_isSharedCheck_1517_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v_r_1440_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1517_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v_size_1457_; lean_object* v_k_1458_; lean_object* v_v_1459_; lean_object* v_l_1460_; lean_object* v_r_1461_; lean_object* v_size_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_size_1457_ = lean_ctor_get(v_l_1445_, 0);
v_k_1458_ = lean_ctor_get(v_l_1445_, 1);
v_v_1459_ = lean_ctor_get(v_l_1445_, 2);
v_l_1460_ = lean_ctor_get(v_l_1445_, 3);
v_r_1461_ = lean_ctor_get(v_l_1445_, 4);
v_size_1462_ = lean_ctor_get(v_r_1446_, 0);
v___x_1463_ = lean_unsigned_to_nat(2u);
v___x_1464_ = lean_nat_mul(v___x_1463_, v_size_1462_);
v___x_1465_ = lean_nat_dec_lt(v_size_1457_, v___x_1464_);
lean_dec(v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1492_; 
lean_inc(v_r_1461_);
lean_inc(v_l_1460_);
lean_inc(v_v_1459_);
lean_inc(v_k_1458_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_l_1445_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; lean_object* v_unused_1497_; 
v_unused_1493_ = lean_ctor_get(v_l_1445_, 4);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1445_, 3);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1445_, 2);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_l_1445_, 1);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_l_1445_, 0);
lean_dec(v_unused_1497_);
v___x_1467_ = v_l_1445_;
v_isShared_1468_ = v_isSharedCheck_1492_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v_l_1445_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1492_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1484_; 
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = lean_nat_add(v___x_1469_, v_size_1441_);
v___x_1471_ = lean_nat_add(v___x_1470_, v_size_1442_);
lean_dec(v_size_1442_);
if (lean_obj_tag(v_l_1460_) == 0)
{
lean_object* v_size_1490_; 
v_size_1490_ = lean_ctor_get(v_l_1460_, 0);
lean_inc(v_size_1490_);
v___y_1484_ = v_size_1490_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___y_1484_ = v___x_1491_;
goto v___jp_1483_;
}
v___jp_1472_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_nat_add(v___y_1473_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec(v___y_1473_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v_r_1446_);
lean_ctor_set(v___x_1467_, 3, v_r_1461_);
lean_ctor_set(v___x_1467_, 2, v_v_1444_);
lean_ctor_set(v___x_1467_, 1, v_k_1443_);
lean_ctor_set(v___x_1467_, 0, v___x_1476_);
v___x_1478_ = v___x_1467_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1443_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1444_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_r_1461_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_r_1446_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v___x_1478_);
lean_ctor_set(v___x_1455_, 3, v___y_1474_);
lean_ctor_set(v___x_1455_, 2, v_v_1459_);
lean_ctor_set(v___x_1455_, 1, v_k_1458_);
lean_ctor_set(v___x_1455_, 0, v___x_1471_);
v___x_1480_ = v___x_1455_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1458_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1459_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v___y_1474_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
v___jp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_nat_add(v___x_1470_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec(v___x_1470_);
v___x_1486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v_k_1437_);
lean_ctor_set(v___x_1486_, 2, v_v_1438_);
lean_ctor_set(v___x_1486_, 3, v_l_1439_);
lean_ctor_set(v___x_1486_, 4, v_l_1460_);
v___x_1487_ = lean_nat_add(v___x_1469_, v_size_1462_);
if (lean_obj_tag(v_r_1461_) == 0)
{
lean_object* v_size_1488_; 
v_size_1488_ = lean_ctor_get(v_r_1461_, 0);
lean_inc(v_size_1488_);
v___y_1473_ = v___x_1487_;
v___y_1474_ = v___x_1486_;
v___y_1475_ = v_size_1488_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___y_1473_ = v___x_1487_;
v___y_1474_ = v___x_1486_;
v___y_1475_ = v___x_1489_;
goto v___jp_1472_;
}
}
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v___x_1498_, v_size_1441_);
v___x_1500_ = lean_nat_add(v___x_1499_, v_size_1442_);
lean_dec(v_size_1442_);
v___x_1501_ = lean_nat_add(v___x_1499_, v_size_1457_);
lean_dec(v___x_1499_);
lean_inc_ref(v_l_1439_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v_l_1445_);
lean_ctor_set(v___x_1455_, 3, v_l_1439_);
lean_ctor_set(v___x_1455_, 2, v_v_1438_);
lean_ctor_set(v___x_1455_, 1, v_k_1437_);
lean_ctor_set(v___x_1455_, 0, v___x_1501_);
v___x_1503_ = v___x_1455_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1437_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1438_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1439_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_l_1445_);
v___x_1503_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_isSharedCheck_1510_ = !lean_is_exclusive(v_l_1439_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; 
v_unused_1511_ = lean_ctor_get(v_l_1439_, 4);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_l_1439_, 3);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1439_, 2);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_l_1439_, 1);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_l_1439_, 0);
lean_dec(v_unused_1515_);
v___x_1505_ = v_l_1439_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v_l_1439_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v_r_1446_);
lean_ctor_set(v___x_1505_, 3, v___x_1503_);
lean_ctor_set(v___x_1505_, 2, v_v_1444_);
lean_ctor_set(v___x_1505_, 1, v_k_1443_);
lean_ctor_set(v___x_1505_, 0, v___x_1500_);
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1443_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1444_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_r_1446_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_size_1523_ = lean_ctor_get(v_l_1439_, 0);
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = lean_nat_add(v___x_1524_, v_size_1523_);
v___x_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v_k_1437_);
lean_ctor_set(v___x_1526_, 2, v_v_1438_);
lean_ctor_set(v___x_1526_, 3, v_l_1439_);
lean_ctor_set(v___x_1526_, 4, v_r_1440_);
return v___x_1526_;
}
}
else
{
if (lean_obj_tag(v_r_1440_) == 0)
{
lean_object* v_l_1527_; 
v_l_1527_ = lean_ctor_get(v_r_1440_, 3);
lean_inc(v_l_1527_);
if (lean_obj_tag(v_l_1527_) == 0)
{
lean_object* v_r_1528_; lean_object* v_k_1529_; lean_object* v_v_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1552_; 
v_r_1528_ = lean_ctor_get(v_r_1440_, 4);
v_k_1529_ = lean_ctor_get(v_r_1440_, 1);
v_v_1530_ = lean_ctor_get(v_r_1440_, 2);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_r_1440_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; lean_object* v_unused_1554_; 
v_unused_1553_ = lean_ctor_get(v_r_1440_, 3);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v_r_1440_, 0);
lean_dec(v_unused_1554_);
v___x_1532_ = v_r_1440_;
v_isShared_1533_ = v_isSharedCheck_1552_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_r_1528_);
lean_inc(v_v_1530_);
lean_inc(v_k_1529_);
lean_dec(v_r_1440_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1552_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1548_; 
v_k_1534_ = lean_ctor_get(v_l_1527_, 1);
v_v_1535_ = lean_ctor_get(v_l_1527_, 2);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_l_1527_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; 
v_unused_1549_ = lean_ctor_get(v_l_1527_, 4);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_l_1527_, 3);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_l_1527_, 0);
lean_dec(v_unused_1551_);
v___x_1537_ = v_l_1527_;
v_isShared_1538_ = v_isSharedCheck_1548_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_v_1535_);
lean_inc(v_k_1534_);
lean_dec(v_l_1527_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1548_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1539_ = lean_unsigned_to_nat(3u);
v___x_1540_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_r_1528_, 2);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 4, v_r_1528_);
lean_ctor_set(v___x_1537_, 3, v_r_1528_);
lean_ctor_set(v___x_1537_, 2, v_v_1438_);
lean_ctor_set(v___x_1537_, 1, v_k_1437_);
lean_ctor_set(v___x_1537_, 0, v___x_1540_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1437_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1438_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_r_1528_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_r_1528_);
v___x_1542_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
lean_inc(v_r_1528_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 3, v_r_1528_);
lean_ctor_set(v___x_1532_, 0, v___x_1540_);
v___x_1544_ = v___x_1532_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1529_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1530_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_r_1528_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_r_1528_);
v___x_1544_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1539_);
lean_ctor_set(v___x_1545_, 1, v_k_1534_);
lean_ctor_set(v___x_1545_, 2, v_v_1535_);
lean_ctor_set(v___x_1545_, 3, v___x_1542_);
lean_ctor_set(v___x_1545_, 4, v___x_1544_);
return v___x_1545_;
}
}
}
}
}
else
{
lean_object* v_r_1555_; 
v_r_1555_ = lean_ctor_get(v_r_1440_, 4);
lean_inc(v_r_1555_);
if (lean_obj_tag(v_r_1555_) == 0)
{
lean_object* v_k_1556_; lean_object* v_v_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1567_; 
v_k_1556_ = lean_ctor_get(v_r_1440_, 1);
v_v_1557_ = lean_ctor_get(v_r_1440_, 2);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_r_1440_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1568_ = lean_ctor_get(v_r_1440_, 4);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_r_1440_, 3);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_r_1440_, 0);
lean_dec(v_unused_1570_);
v___x_1559_ = v_r_1440_;
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_v_1557_);
lean_inc(v_k_1556_);
lean_dec(v_r_1440_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1561_ = lean_unsigned_to_nat(3u);
v___x_1562_ = lean_unsigned_to_nat(1u);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v_l_1527_);
lean_ctor_set(v___x_1559_, 2, v_v_1438_);
lean_ctor_set(v___x_1559_, 1, v_k_1437_);
lean_ctor_set(v___x_1559_, 0, v___x_1562_);
v___x_1564_ = v___x_1559_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1437_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1438_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v_l_1527_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v_l_1527_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1561_);
lean_ctor_set(v___x_1565_, 1, v_k_1556_);
lean_ctor_set(v___x_1565_, 2, v_v_1557_);
lean_ctor_set(v___x_1565_, 3, v___x_1564_);
lean_ctor_set(v___x_1565_, 4, v_r_1555_);
return v___x_1565_;
}
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_unsigned_to_nat(2u);
v___x_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_k_1437_);
lean_ctor_set(v___x_1572_, 2, v_v_1438_);
lean_ctor_set(v___x_1572_, 3, v_r_1555_);
lean_ctor_set(v___x_1572_, 4, v_r_1440_);
return v___x_1572_;
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_k_1437_);
lean_ctor_set(v___x_1574_, 2, v_v_1438_);
lean_ctor_set(v___x_1574_, 3, v_r_1440_);
lean_ctor_set(v___x_1574_, 4, v_r_1440_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_k_1577_, lean_object* v_v_1578_, lean_object* v_l_1579_, lean_object* v_r_1580_, lean_object* v_hlb_1581_, lean_object* v_hrb_1582_, lean_object* v_hlr_1583_){
_start:
{
if (lean_obj_tag(v_l_1579_) == 0)
{
if (lean_obj_tag(v_r_1580_) == 0)
{
lean_object* v_size_1584_; lean_object* v_size_1585_; lean_object* v_k_1586_; lean_object* v_v_1587_; lean_object* v_l_1588_; lean_object* v_r_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_size_1584_ = lean_ctor_get(v_l_1579_, 0);
v_size_1585_ = lean_ctor_get(v_r_1580_, 0);
v_k_1586_ = lean_ctor_get(v_r_1580_, 1);
v_v_1587_ = lean_ctor_get(v_r_1580_, 2);
v_l_1588_ = lean_ctor_get(v_r_1580_, 3);
lean_inc(v_l_1588_);
v_r_1589_ = lean_ctor_get(v_r_1580_, 4);
v___x_1590_ = lean_unsigned_to_nat(3u);
v___x_1591_ = lean_nat_mul(v___x_1590_, v_size_1584_);
v___x_1592_ = lean_nat_dec_lt(v___x_1591_, v_size_1585_);
lean_dec(v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_l_1588_);
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v___x_1593_, v_size_1584_);
v___x_1595_ = lean_nat_add(v___x_1594_, v_size_1585_);
lean_dec(v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_k_1577_);
lean_ctor_set(v___x_1596_, 2, v_v_1578_);
lean_ctor_set(v___x_1596_, 3, v_l_1579_);
lean_ctor_set(v___x_1596_, 4, v_r_1580_);
return v___x_1596_;
}
else
{
lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1660_; 
lean_inc(v_r_1589_);
lean_inc(v_v_1587_);
lean_inc(v_k_1586_);
lean_inc(v_size_1585_);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_r_1580_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; lean_object* v_unused_1664_; lean_object* v_unused_1665_; 
v_unused_1661_ = lean_ctor_get(v_r_1580_, 4);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_r_1580_, 3);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_r_1580_, 2);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_r_1580_, 1);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_r_1580_, 0);
lean_dec(v_unused_1665_);
v___x_1598_ = v_r_1580_;
v_isShared_1599_ = v_isSharedCheck_1660_;
goto v_resetjp_1597_;
}
else
{
lean_dec(v_r_1580_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1660_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_size_1600_; lean_object* v_k_1601_; lean_object* v_v_1602_; lean_object* v_l_1603_; lean_object* v_r_1604_; lean_object* v_size_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_size_1600_ = lean_ctor_get(v_l_1588_, 0);
v_k_1601_ = lean_ctor_get(v_l_1588_, 1);
v_v_1602_ = lean_ctor_get(v_l_1588_, 2);
v_l_1603_ = lean_ctor_get(v_l_1588_, 3);
v_r_1604_ = lean_ctor_get(v_l_1588_, 4);
v_size_1605_ = lean_ctor_get(v_r_1589_, 0);
v___x_1606_ = lean_unsigned_to_nat(2u);
v___x_1607_ = lean_nat_mul(v___x_1606_, v_size_1605_);
v___x_1608_ = lean_nat_dec_lt(v_size_1600_, v___x_1607_);
lean_dec(v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1635_; 
lean_inc(v_r_1604_);
lean_inc(v_l_1603_);
lean_inc(v_v_1602_);
lean_inc(v_k_1601_);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_l_1588_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; 
v_unused_1636_ = lean_ctor_get(v_l_1588_, 4);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_l_1588_, 3);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_l_1588_, 2);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_l_1588_, 1);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_l_1588_, 0);
lean_dec(v_unused_1640_);
v___x_1610_ = v_l_1588_;
v_isShared_1611_ = v_isSharedCheck_1635_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v_l_1588_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1635_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1627_; 
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_add(v___x_1612_, v_size_1584_);
v___x_1614_ = lean_nat_add(v___x_1613_, v_size_1585_);
lean_dec(v_size_1585_);
if (lean_obj_tag(v_l_1603_) == 0)
{
lean_object* v_size_1633_; 
v_size_1633_ = lean_ctor_get(v_l_1603_, 0);
lean_inc(v_size_1633_);
v___y_1627_ = v_size_1633_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
v___y_1627_ = v___x_1634_;
goto v___jp_1626_;
}
v___jp_1615_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_nat_add(v___y_1616_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec(v___y_1616_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 4, v_r_1589_);
lean_ctor_set(v___x_1610_, 3, v_r_1604_);
lean_ctor_set(v___x_1610_, 2, v_v_1587_);
lean_ctor_set(v___x_1610_, 1, v_k_1586_);
lean_ctor_set(v___x_1610_, 0, v___x_1619_);
v___x_1621_ = v___x_1610_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_k_1586_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_v_1587_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_r_1604_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_r_1589_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 4, v___x_1621_);
lean_ctor_set(v___x_1598_, 3, v___y_1617_);
lean_ctor_set(v___x_1598_, 2, v_v_1602_);
lean_ctor_set(v___x_1598_, 1, v_k_1601_);
lean_ctor_set(v___x_1598_, 0, v___x_1614_);
v___x_1623_ = v___x_1598_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_k_1601_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_v_1602_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v___y_1617_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_nat_add(v___x_1613_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec(v___x_1613_);
v___x_1629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_k_1577_);
lean_ctor_set(v___x_1629_, 2, v_v_1578_);
lean_ctor_set(v___x_1629_, 3, v_l_1579_);
lean_ctor_set(v___x_1629_, 4, v_l_1603_);
v___x_1630_ = lean_nat_add(v___x_1612_, v_size_1605_);
if (lean_obj_tag(v_r_1604_) == 0)
{
lean_object* v_size_1631_; 
v_size_1631_ = lean_ctor_get(v_r_1604_, 0);
lean_inc(v_size_1631_);
v___y_1616_ = v___x_1630_;
v___y_1617_ = v___x_1629_;
v___y_1618_ = v_size_1631_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___y_1616_ = v___x_1630_;
v___y_1617_ = v___x_1629_;
v___y_1618_ = v___x_1632_;
goto v___jp_1615_;
}
}
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_nat_add(v___x_1641_, v_size_1584_);
v___x_1643_ = lean_nat_add(v___x_1642_, v_size_1585_);
lean_dec(v_size_1585_);
v___x_1644_ = lean_nat_add(v___x_1642_, v_size_1600_);
lean_dec(v___x_1642_);
lean_inc_ref(v_l_1579_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 4, v_l_1588_);
lean_ctor_set(v___x_1598_, 3, v_l_1579_);
lean_ctor_set(v___x_1598_, 2, v_v_1578_);
lean_ctor_set(v___x_1598_, 1, v_k_1577_);
lean_ctor_set(v___x_1598_, 0, v___x_1644_);
v___x_1646_ = v___x_1598_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v_l_1579_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v_l_1588_);
v___x_1646_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_isSharedCheck_1653_ = !lean_is_exclusive(v_l_1579_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1654_ = lean_ctor_get(v_l_1579_, 4);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_l_1579_, 3);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_l_1579_, 2);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_l_1579_, 1);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_l_1579_, 0);
lean_dec(v_unused_1658_);
v___x_1648_ = v_l_1579_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v_l_1579_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v_r_1589_);
lean_ctor_set(v___x_1648_, 3, v___x_1646_);
lean_ctor_set(v___x_1648_, 2, v_v_1587_);
lean_ctor_set(v___x_1648_, 1, v_k_1586_);
lean_ctor_set(v___x_1648_, 0, v___x_1643_);
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1586_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1587_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_r_1589_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_size_1666_ = lean_ctor_get(v_l_1579_, 0);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v___x_1667_, v_size_1666_);
v___x_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v_k_1577_);
lean_ctor_set(v___x_1669_, 2, v_v_1578_);
lean_ctor_set(v___x_1669_, 3, v_l_1579_);
lean_ctor_set(v___x_1669_, 4, v_r_1580_);
return v___x_1669_;
}
}
else
{
if (lean_obj_tag(v_r_1580_) == 0)
{
lean_object* v_l_1670_; 
v_l_1670_ = lean_ctor_get(v_r_1580_, 3);
lean_inc(v_l_1670_);
if (lean_obj_tag(v_l_1670_) == 0)
{
lean_object* v_r_1671_; lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1695_; 
v_r_1671_ = lean_ctor_get(v_r_1580_, 4);
v_k_1672_ = lean_ctor_get(v_r_1580_, 1);
v_v_1673_ = lean_ctor_get(v_r_1580_, 2);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_r_1580_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; 
v_unused_1696_ = lean_ctor_get(v_r_1580_, 3);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_r_1580_, 0);
lean_dec(v_unused_1697_);
v___x_1675_ = v_r_1580_;
v_isShared_1676_ = v_isSharedCheck_1695_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_r_1671_);
lean_inc(v_v_1673_);
lean_inc(v_k_1672_);
lean_dec(v_r_1580_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1695_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_k_1677_; lean_object* v_v_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1691_; 
v_k_1677_ = lean_ctor_get(v_l_1670_, 1);
v_v_1678_ = lean_ctor_get(v_l_1670_, 2);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_l_1670_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; 
v_unused_1692_ = lean_ctor_get(v_l_1670_, 4);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_l_1670_, 3);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_l_1670_, 0);
lean_dec(v_unused_1694_);
v___x_1680_ = v_l_1670_;
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_v_1678_);
lean_inc(v_k_1677_);
lean_dec(v_l_1670_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1682_ = lean_unsigned_to_nat(3u);
v___x_1683_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_r_1671_, 2);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 4, v_r_1671_);
lean_ctor_set(v___x_1680_, 3, v_r_1671_);
lean_ctor_set(v___x_1680_, 2, v_v_1578_);
lean_ctor_set(v___x_1680_, 1, v_k_1577_);
lean_ctor_set(v___x_1680_, 0, v___x_1683_);
v___x_1685_ = v___x_1680_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_r_1671_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_r_1671_);
v___x_1685_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
lean_inc(v_r_1671_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 3, v_r_1671_);
lean_ctor_set(v___x_1675_, 0, v___x_1683_);
v___x_1687_ = v___x_1675_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_r_1671_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_r_1671_);
v___x_1687_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1682_);
lean_ctor_set(v___x_1688_, 1, v_k_1677_);
lean_ctor_set(v___x_1688_, 2, v_v_1678_);
lean_ctor_set(v___x_1688_, 3, v___x_1685_);
lean_ctor_set(v___x_1688_, 4, v___x_1687_);
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v_r_1698_; 
v_r_1698_ = lean_ctor_get(v_r_1580_, 4);
lean_inc(v_r_1698_);
if (lean_obj_tag(v_r_1698_) == 0)
{
lean_object* v_k_1699_; lean_object* v_v_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1710_; 
v_k_1699_ = lean_ctor_get(v_r_1580_, 1);
v_v_1700_ = lean_ctor_get(v_r_1580_, 2);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_r_1580_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; lean_object* v_unused_1712_; lean_object* v_unused_1713_; 
v_unused_1711_ = lean_ctor_get(v_r_1580_, 4);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_r_1580_, 3);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v_r_1580_, 0);
lean_dec(v_unused_1713_);
v___x_1702_ = v_r_1580_;
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_v_1700_);
lean_inc(v_k_1699_);
lean_dec(v_r_1580_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1704_ = lean_unsigned_to_nat(3u);
v___x_1705_ = lean_unsigned_to_nat(1u);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 4, v_l_1670_);
lean_ctor_set(v___x_1702_, 2, v_v_1578_);
lean_ctor_set(v___x_1702_, 1, v_k_1577_);
lean_ctor_set(v___x_1702_, 0, v___x_1705_);
v___x_1707_ = v___x_1702_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_l_1670_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v_l_1670_);
v___x_1707_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1704_);
lean_ctor_set(v___x_1708_, 1, v_k_1699_);
lean_ctor_set(v___x_1708_, 2, v_v_1700_);
lean_ctor_set(v___x_1708_, 3, v___x_1707_);
lean_ctor_set(v___x_1708_, 4, v_r_1698_);
return v___x_1708_;
}
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_unsigned_to_nat(2u);
v___x_1715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v_k_1577_);
lean_ctor_set(v___x_1715_, 2, v_v_1578_);
lean_ctor_set(v___x_1715_, 3, v_r_1698_);
lean_ctor_set(v___x_1715_, 4, v_r_1580_);
return v___x_1715_;
}
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v_k_1577_);
lean_ctor_set(v___x_1717_, 2, v_v_1578_);
lean_ctor_set(v___x_1717_, 3, v_r_1580_);
lean_ctor_set(v___x_1717_, 4, v_r_1580_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase___redArg(lean_object* v_k_1718_, lean_object* v_v_1719_, lean_object* v_l_1720_, lean_object* v_r_1721_){
_start:
{
if (lean_obj_tag(v_l_1720_) == 0)
{
if (lean_obj_tag(v_r_1721_) == 0)
{
lean_object* v_size_1722_; lean_object* v_size_1723_; lean_object* v_k_1724_; lean_object* v_v_1725_; lean_object* v_l_1726_; lean_object* v_r_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_size_1722_ = lean_ctor_get(v_l_1720_, 0);
v_size_1723_ = lean_ctor_get(v_r_1721_, 0);
v_k_1724_ = lean_ctor_get(v_r_1721_, 1);
v_v_1725_ = lean_ctor_get(v_r_1721_, 2);
v_l_1726_ = lean_ctor_get(v_r_1721_, 3);
lean_inc(v_l_1726_);
v_r_1727_ = lean_ctor_get(v_r_1721_, 4);
v___x_1728_ = lean_unsigned_to_nat(3u);
v___x_1729_ = lean_nat_mul(v___x_1728_, v_size_1722_);
v___x_1730_ = lean_nat_dec_lt(v___x_1729_, v_size_1723_);
lean_dec(v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v_l_1726_);
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_add(v___x_1731_, v_size_1722_);
v___x_1733_ = lean_nat_add(v___x_1732_, v_size_1723_);
lean_dec(v___x_1732_);
v___x_1734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v_k_1718_);
lean_ctor_set(v___x_1734_, 2, v_v_1719_);
lean_ctor_set(v___x_1734_, 3, v_l_1720_);
lean_ctor_set(v___x_1734_, 4, v_r_1721_);
return v___x_1734_;
}
else
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1798_; 
lean_inc(v_r_1727_);
lean_inc(v_v_1725_);
lean_inc(v_k_1724_);
lean_inc(v_size_1723_);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_r_1721_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; 
v_unused_1799_ = lean_ctor_get(v_r_1721_, 4);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_r_1721_, 3);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_r_1721_, 2);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_r_1721_, 1);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_r_1721_, 0);
lean_dec(v_unused_1803_);
v___x_1736_ = v_r_1721_;
v_isShared_1737_ = v_isSharedCheck_1798_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v_r_1721_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1798_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_size_1738_; lean_object* v_k_1739_; lean_object* v_v_1740_; lean_object* v_l_1741_; lean_object* v_r_1742_; lean_object* v_size_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v_size_1738_ = lean_ctor_get(v_l_1726_, 0);
v_k_1739_ = lean_ctor_get(v_l_1726_, 1);
v_v_1740_ = lean_ctor_get(v_l_1726_, 2);
v_l_1741_ = lean_ctor_get(v_l_1726_, 3);
v_r_1742_ = lean_ctor_get(v_l_1726_, 4);
v_size_1743_ = lean_ctor_get(v_r_1727_, 0);
v___x_1744_ = lean_unsigned_to_nat(2u);
v___x_1745_ = lean_nat_mul(v___x_1744_, v_size_1743_);
v___x_1746_ = lean_nat_dec_lt(v_size_1738_, v___x_1745_);
lean_dec(v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1773_; 
lean_inc(v_r_1742_);
lean_inc(v_l_1741_);
lean_inc(v_v_1740_);
lean_inc(v_k_1739_);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_l_1726_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; 
v_unused_1774_ = lean_ctor_get(v_l_1726_, 4);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_l_1726_, 3);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_l_1726_, 2);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_l_1726_, 1);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_l_1726_, 0);
lean_dec(v_unused_1778_);
v___x_1748_ = v_l_1726_;
v_isShared_1749_ = v_isSharedCheck_1773_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v_l_1726_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1773_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1765_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v___x_1750_, v_size_1722_);
v___x_1752_ = lean_nat_add(v___x_1751_, v_size_1723_);
lean_dec(v_size_1723_);
if (lean_obj_tag(v_l_1741_) == 0)
{
lean_object* v_size_1771_; 
v_size_1771_ = lean_ctor_get(v_l_1741_, 0);
lean_inc(v_size_1771_);
v___y_1765_ = v_size_1771_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_unsigned_to_nat(0u);
v___y_1765_ = v___x_1772_;
goto v___jp_1764_;
}
v___jp_1753_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_nat_add(v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec(v___y_1755_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v_r_1727_);
lean_ctor_set(v___x_1748_, 3, v_r_1742_);
lean_ctor_set(v___x_1748_, 2, v_v_1725_);
lean_ctor_set(v___x_1748_, 1, v_k_1724_);
lean_ctor_set(v___x_1748_, 0, v___x_1757_);
v___x_1759_ = v___x_1748_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_r_1742_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_r_1727_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 4, v___x_1759_);
lean_ctor_set(v___x_1736_, 3, v___y_1754_);
lean_ctor_set(v___x_1736_, 2, v_v_1740_);
lean_ctor_set(v___x_1736_, 1, v_k_1739_);
lean_ctor_set(v___x_1736_, 0, v___x_1752_);
v___x_1761_ = v___x_1736_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1739_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1740_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v___y_1754_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
v___jp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_nat_add(v___x_1751_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec(v___x_1751_);
v___x_1767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_k_1718_);
lean_ctor_set(v___x_1767_, 2, v_v_1719_);
lean_ctor_set(v___x_1767_, 3, v_l_1720_);
lean_ctor_set(v___x_1767_, 4, v_l_1741_);
v___x_1768_ = lean_nat_add(v___x_1750_, v_size_1743_);
if (lean_obj_tag(v_r_1742_) == 0)
{
lean_object* v_size_1769_; 
v_size_1769_ = lean_ctor_get(v_r_1742_, 0);
lean_inc(v_size_1769_);
v___y_1754_ = v___x_1767_;
v___y_1755_ = v___x_1768_;
v___y_1756_ = v_size_1769_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___y_1754_ = v___x_1767_;
v___y_1755_ = v___x_1768_;
v___y_1756_ = v___x_1770_;
goto v___jp_1753_;
}
}
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_nat_add(v___x_1779_, v_size_1722_);
v___x_1781_ = lean_nat_add(v___x_1780_, v_size_1723_);
lean_dec(v_size_1723_);
v___x_1782_ = lean_nat_add(v___x_1780_, v_size_1738_);
lean_dec(v___x_1780_);
lean_inc_ref(v_l_1720_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 4, v_l_1726_);
lean_ctor_set(v___x_1736_, 3, v_l_1720_);
lean_ctor_set(v___x_1736_, 2, v_v_1719_);
lean_ctor_set(v___x_1736_, 1, v_k_1718_);
lean_ctor_set(v___x_1736_, 0, v___x_1782_);
v___x_1784_ = v___x_1736_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_l_1720_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_l_1726_);
v___x_1784_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_isSharedCheck_1791_ = !lean_is_exclusive(v_l_1720_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; lean_object* v_unused_1793_; lean_object* v_unused_1794_; lean_object* v_unused_1795_; lean_object* v_unused_1796_; 
v_unused_1792_ = lean_ctor_get(v_l_1720_, 4);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_l_1720_, 3);
lean_dec(v_unused_1793_);
v_unused_1794_ = lean_ctor_get(v_l_1720_, 2);
lean_dec(v_unused_1794_);
v_unused_1795_ = lean_ctor_get(v_l_1720_, 1);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_l_1720_, 0);
lean_dec(v_unused_1796_);
v___x_1786_ = v_l_1720_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_dec(v_l_1720_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 4, v_r_1727_);
lean_ctor_set(v___x_1786_, 3, v___x_1784_);
lean_ctor_set(v___x_1786_, 2, v_v_1725_);
lean_ctor_set(v___x_1786_, 1, v_k_1724_);
lean_ctor_set(v___x_1786_, 0, v___x_1781_);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_r_1727_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_size_1804_ = lean_ctor_get(v_l_1720_, 0);
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = lean_nat_add(v___x_1805_, v_size_1804_);
v___x_1807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v_k_1718_);
lean_ctor_set(v___x_1807_, 2, v_v_1719_);
lean_ctor_set(v___x_1807_, 3, v_l_1720_);
lean_ctor_set(v___x_1807_, 4, v_r_1721_);
return v___x_1807_;
}
}
else
{
if (lean_obj_tag(v_r_1721_) == 0)
{
lean_object* v_l_1808_; 
v_l_1808_ = lean_ctor_get(v_r_1721_, 3);
lean_inc(v_l_1808_);
if (lean_obj_tag(v_l_1808_) == 0)
{
lean_object* v_r_1809_; 
v_r_1809_ = lean_ctor_get(v_r_1721_, 4);
lean_inc(v_r_1809_);
if (lean_obj_tag(v_r_1809_) == 0)
{
lean_object* v_size_1810_; lean_object* v_k_1811_; lean_object* v_v_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1824_; 
v_size_1810_ = lean_ctor_get(v_r_1721_, 0);
v_k_1811_ = lean_ctor_get(v_r_1721_, 1);
v_v_1812_ = lean_ctor_get(v_r_1721_, 2);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_r_1721_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; lean_object* v_unused_1826_; 
v_unused_1825_ = lean_ctor_get(v_r_1721_, 4);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_r_1721_, 3);
lean_dec(v_unused_1826_);
v___x_1814_ = v_r_1721_;
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_v_1812_);
lean_inc(v_k_1811_);
lean_inc(v_size_1810_);
lean_dec(v_r_1721_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_size_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v_size_1816_ = lean_ctor_get(v_l_1808_, 0);
v___x_1817_ = lean_unsigned_to_nat(1u);
v___x_1818_ = lean_nat_add(v___x_1817_, v_size_1810_);
lean_dec(v_size_1810_);
v___x_1819_ = lean_nat_add(v___x_1817_, v_size_1816_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 4, v_l_1808_);
lean_ctor_set(v___x_1814_, 3, v_l_1720_);
lean_ctor_set(v___x_1814_, 2, v_v_1719_);
lean_ctor_set(v___x_1814_, 1, v_k_1718_);
lean_ctor_set(v___x_1814_, 0, v___x_1819_);
v___x_1821_ = v___x_1814_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_l_1720_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_l_1808_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1818_);
lean_ctor_set(v___x_1822_, 1, v_k_1811_);
lean_ctor_set(v___x_1822_, 2, v_v_1812_);
lean_ctor_set(v___x_1822_, 3, v___x_1821_);
lean_ctor_set(v___x_1822_, 4, v_r_1809_);
return v___x_1822_;
}
}
}
else
{
lean_object* v_k_1827_; lean_object* v_v_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1850_; 
v_k_1827_ = lean_ctor_get(v_r_1721_, 1);
v_v_1828_ = lean_ctor_get(v_r_1721_, 2);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_r_1721_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; 
v_unused_1851_ = lean_ctor_get(v_r_1721_, 4);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_r_1721_, 3);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_r_1721_, 0);
lean_dec(v_unused_1853_);
v___x_1830_ = v_r_1721_;
v_isShared_1831_ = v_isSharedCheck_1850_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_v_1828_);
lean_inc(v_k_1827_);
lean_dec(v_r_1721_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1850_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_k_1832_; lean_object* v_v_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1846_; 
v_k_1832_ = lean_ctor_get(v_l_1808_, 1);
v_v_1833_ = lean_ctor_get(v_l_1808_, 2);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_l_1808_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; 
v_unused_1847_ = lean_ctor_get(v_l_1808_, 4);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v_l_1808_, 3);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_l_1808_, 0);
lean_dec(v_unused_1849_);
v___x_1835_ = v_l_1808_;
v_isShared_1836_ = v_isSharedCheck_1846_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_v_1833_);
lean_inc(v_k_1832_);
lean_dec(v_l_1808_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1846_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1837_ = lean_unsigned_to_nat(3u);
v___x_1838_ = lean_unsigned_to_nat(1u);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 4, v_r_1809_);
lean_ctor_set(v___x_1835_, 3, v_r_1809_);
lean_ctor_set(v___x_1835_, 2, v_v_1719_);
lean_ctor_set(v___x_1835_, 1, v_k_1718_);
lean_ctor_set(v___x_1835_, 0, v___x_1838_);
v___x_1840_ = v___x_1835_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_r_1809_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_r_1809_);
v___x_1840_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 3, v_r_1809_);
lean_ctor_set(v___x_1830_, 0, v___x_1838_);
v___x_1842_ = v___x_1830_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_k_1827_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_v_1828_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_r_1809_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_r_1809_);
v___x_1842_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1837_);
lean_ctor_set(v___x_1843_, 1, v_k_1832_);
lean_ctor_set(v___x_1843_, 2, v_v_1833_);
lean_ctor_set(v___x_1843_, 3, v___x_1840_);
lean_ctor_set(v___x_1843_, 4, v___x_1842_);
return v___x_1843_;
}
}
}
}
}
}
else
{
lean_object* v_r_1854_; 
v_r_1854_ = lean_ctor_get(v_r_1721_, 4);
lean_inc(v_r_1854_);
if (lean_obj_tag(v_r_1854_) == 0)
{
lean_object* v_k_1855_; lean_object* v_v_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1866_; 
v_k_1855_ = lean_ctor_get(v_r_1721_, 1);
v_v_1856_ = lean_ctor_get(v_r_1721_, 2);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_r_1721_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; lean_object* v_unused_1868_; lean_object* v_unused_1869_; 
v_unused_1867_ = lean_ctor_get(v_r_1721_, 4);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_r_1721_, 3);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v_r_1721_, 0);
lean_dec(v_unused_1869_);
v___x_1858_ = v_r_1721_;
v_isShared_1859_ = v_isSharedCheck_1866_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_v_1856_);
lean_inc(v_k_1855_);
lean_dec(v_r_1721_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1866_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1860_ = lean_unsigned_to_nat(3u);
v___x_1861_ = lean_unsigned_to_nat(1u);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 4, v_l_1808_);
lean_ctor_set(v___x_1858_, 2, v_v_1719_);
lean_ctor_set(v___x_1858_, 1, v_k_1718_);
lean_ctor_set(v___x_1858_, 0, v___x_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_l_1808_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v_l_1808_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1860_);
lean_ctor_set(v___x_1864_, 1, v_k_1855_);
lean_ctor_set(v___x_1864_, 2, v_v_1856_);
lean_ctor_set(v___x_1864_, 3, v___x_1863_);
lean_ctor_set(v___x_1864_, 4, v_r_1854_);
return v___x_1864_;
}
}
}
else
{
lean_object* v_size_1870_; lean_object* v_k_1871_; lean_object* v_v_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1881_; 
v_size_1870_ = lean_ctor_get(v_r_1721_, 0);
v_k_1871_ = lean_ctor_get(v_r_1721_, 1);
v_v_1872_ = lean_ctor_get(v_r_1721_, 2);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_r_1721_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; lean_object* v_unused_1883_; 
v_unused_1882_ = lean_ctor_get(v_r_1721_, 4);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_r_1721_, 3);
lean_dec(v_unused_1883_);
v___x_1874_ = v_r_1721_;
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_v_1872_);
lean_inc(v_k_1871_);
lean_inc(v_size_1870_);
lean_dec(v_r_1721_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 3, v_r_1854_);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_size_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_k_1871_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_v_1872_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_r_1854_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v_r_1854_);
v___x_1877_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_unsigned_to_nat(2u);
v___x_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v_k_1718_);
lean_ctor_set(v___x_1879_, 2, v_v_1719_);
lean_ctor_set(v___x_1879_, 3, v_r_1854_);
lean_ctor_set(v___x_1879_, 4, v___x_1877_);
return v___x_1879_;
}
}
}
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v_k_1718_);
lean_ctor_set(v___x_1885_, 2, v_v_1719_);
lean_ctor_set(v___x_1885_, 3, v_r_1721_);
lean_ctor_set(v___x_1885_, 4, v_r_1721_);
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase(lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_k_1888_, lean_object* v_v_1889_, lean_object* v_l_1890_, lean_object* v_r_1891_, lean_object* v_hlb_1892_, lean_object* v_hrb_1893_, lean_object* v_hlr_1894_){
_start:
{
if (lean_obj_tag(v_l_1890_) == 0)
{
if (lean_obj_tag(v_r_1891_) == 0)
{
lean_object* v_size_1895_; lean_object* v_size_1896_; lean_object* v_k_1897_; lean_object* v_v_1898_; lean_object* v_l_1899_; lean_object* v_r_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_size_1895_ = lean_ctor_get(v_l_1890_, 0);
v_size_1896_ = lean_ctor_get(v_r_1891_, 0);
v_k_1897_ = lean_ctor_get(v_r_1891_, 1);
v_v_1898_ = lean_ctor_get(v_r_1891_, 2);
v_l_1899_ = lean_ctor_get(v_r_1891_, 3);
lean_inc(v_l_1899_);
v_r_1900_ = lean_ctor_get(v_r_1891_, 4);
v___x_1901_ = lean_unsigned_to_nat(3u);
v___x_1902_ = lean_nat_mul(v___x_1901_, v_size_1895_);
v___x_1903_ = lean_nat_dec_lt(v___x_1902_, v_size_1896_);
lean_dec(v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec(v_l_1899_);
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v___x_1904_, v_size_1895_);
v___x_1906_ = lean_nat_add(v___x_1905_, v_size_1896_);
lean_dec(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v_k_1888_);
lean_ctor_set(v___x_1907_, 2, v_v_1889_);
lean_ctor_set(v___x_1907_, 3, v_l_1890_);
lean_ctor_set(v___x_1907_, 4, v_r_1891_);
return v___x_1907_;
}
else
{
lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1971_; 
lean_inc(v_r_1900_);
lean_inc(v_v_1898_);
lean_inc(v_k_1897_);
lean_inc(v_size_1896_);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_r_1891_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; lean_object* v_unused_1973_; lean_object* v_unused_1974_; lean_object* v_unused_1975_; lean_object* v_unused_1976_; 
v_unused_1972_ = lean_ctor_get(v_r_1891_, 4);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v_r_1891_, 3);
lean_dec(v_unused_1973_);
v_unused_1974_ = lean_ctor_get(v_r_1891_, 2);
lean_dec(v_unused_1974_);
v_unused_1975_ = lean_ctor_get(v_r_1891_, 1);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_r_1891_, 0);
lean_dec(v_unused_1976_);
v___x_1909_ = v_r_1891_;
v_isShared_1910_ = v_isSharedCheck_1971_;
goto v_resetjp_1908_;
}
else
{
lean_dec(v_r_1891_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1971_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_size_1911_; lean_object* v_k_1912_; lean_object* v_v_1913_; lean_object* v_l_1914_; lean_object* v_r_1915_; lean_object* v_size_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v_size_1911_ = lean_ctor_get(v_l_1899_, 0);
v_k_1912_ = lean_ctor_get(v_l_1899_, 1);
v_v_1913_ = lean_ctor_get(v_l_1899_, 2);
v_l_1914_ = lean_ctor_get(v_l_1899_, 3);
v_r_1915_ = lean_ctor_get(v_l_1899_, 4);
v_size_1916_ = lean_ctor_get(v_r_1900_, 0);
v___x_1917_ = lean_unsigned_to_nat(2u);
v___x_1918_ = lean_nat_mul(v___x_1917_, v_size_1916_);
v___x_1919_ = lean_nat_dec_lt(v_size_1911_, v___x_1918_);
lean_dec(v___x_1918_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1946_; 
lean_inc(v_r_1915_);
lean_inc(v_l_1914_);
lean_inc(v_v_1913_);
lean_inc(v_k_1912_);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_l_1899_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; lean_object* v_unused_1948_; lean_object* v_unused_1949_; lean_object* v_unused_1950_; lean_object* v_unused_1951_; 
v_unused_1947_ = lean_ctor_get(v_l_1899_, 4);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_l_1899_, 3);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_l_1899_, 2);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_l_1899_, 1);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_l_1899_, 0);
lean_dec(v_unused_1951_);
v___x_1921_ = v_l_1899_;
v_isShared_1922_ = v_isSharedCheck_1946_;
goto v_resetjp_1920_;
}
else
{
lean_dec(v_l_1899_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1946_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1938_; 
v___x_1923_ = lean_unsigned_to_nat(1u);
v___x_1924_ = lean_nat_add(v___x_1923_, v_size_1895_);
v___x_1925_ = lean_nat_add(v___x_1924_, v_size_1896_);
lean_dec(v_size_1896_);
if (lean_obj_tag(v_l_1914_) == 0)
{
lean_object* v_size_1944_; 
v_size_1944_ = lean_ctor_get(v_l_1914_, 0);
lean_inc(v_size_1944_);
v___y_1938_ = v_size_1944_;
goto v___jp_1937_;
}
else
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___y_1938_ = v___x_1945_;
goto v___jp_1937_;
}
v___jp_1926_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_nat_add(v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 4, v_r_1900_);
lean_ctor_set(v___x_1921_, 3, v_r_1915_);
lean_ctor_set(v___x_1921_, 2, v_v_1898_);
lean_ctor_set(v___x_1921_, 1, v_k_1897_);
lean_ctor_set(v___x_1921_, 0, v___x_1930_);
v___x_1932_ = v___x_1921_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_k_1897_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_v_1898_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_r_1915_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v_r_1900_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 4, v___x_1932_);
lean_ctor_set(v___x_1909_, 3, v___y_1927_);
lean_ctor_set(v___x_1909_, 2, v_v_1913_);
lean_ctor_set(v___x_1909_, 1, v_k_1912_);
lean_ctor_set(v___x_1909_, 0, v___x_1925_);
v___x_1934_ = v___x_1909_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_k_1912_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_v_1913_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v___y_1927_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
v___jp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = lean_nat_add(v___x_1924_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec(v___x_1924_);
v___x_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_k_1888_);
lean_ctor_set(v___x_1940_, 2, v_v_1889_);
lean_ctor_set(v___x_1940_, 3, v_l_1890_);
lean_ctor_set(v___x_1940_, 4, v_l_1914_);
v___x_1941_ = lean_nat_add(v___x_1923_, v_size_1916_);
if (lean_obj_tag(v_r_1915_) == 0)
{
lean_object* v_size_1942_; 
v_size_1942_ = lean_ctor_get(v_r_1915_, 0);
lean_inc(v_size_1942_);
v___y_1927_ = v___x_1940_;
v___y_1928_ = v___x_1941_;
v___y_1929_ = v_size_1942_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_unsigned_to_nat(0u);
v___y_1927_ = v___x_1940_;
v___y_1928_ = v___x_1941_;
v___y_1929_ = v___x_1943_;
goto v___jp_1926_;
}
}
}
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1952_ = lean_unsigned_to_nat(1u);
v___x_1953_ = lean_nat_add(v___x_1952_, v_size_1895_);
v___x_1954_ = lean_nat_add(v___x_1953_, v_size_1896_);
lean_dec(v_size_1896_);
v___x_1955_ = lean_nat_add(v___x_1953_, v_size_1911_);
lean_dec(v___x_1953_);
lean_inc_ref(v_l_1890_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 4, v_l_1899_);
lean_ctor_set(v___x_1909_, 3, v_l_1890_);
lean_ctor_set(v___x_1909_, 2, v_v_1889_);
lean_ctor_set(v___x_1909_, 1, v_k_1888_);
lean_ctor_set(v___x_1909_, 0, v___x_1955_);
v___x_1957_ = v___x_1909_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_k_1888_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_v_1889_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_l_1890_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v_l_1899_);
v___x_1957_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_isSharedCheck_1964_ = !lean_is_exclusive(v_l_1890_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; lean_object* v_unused_1966_; lean_object* v_unused_1967_; lean_object* v_unused_1968_; lean_object* v_unused_1969_; 
v_unused_1965_ = lean_ctor_get(v_l_1890_, 4);
lean_dec(v_unused_1965_);
v_unused_1966_ = lean_ctor_get(v_l_1890_, 3);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_l_1890_, 2);
lean_dec(v_unused_1967_);
v_unused_1968_ = lean_ctor_get(v_l_1890_, 1);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_l_1890_, 0);
lean_dec(v_unused_1969_);
v___x_1959_ = v_l_1890_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v_l_1890_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 4, v_r_1900_);
lean_ctor_set(v___x_1959_, 3, v___x_1957_);
lean_ctor_set(v___x_1959_, 2, v_v_1898_);
lean_ctor_set(v___x_1959_, 1, v_k_1897_);
lean_ctor_set(v___x_1959_, 0, v___x_1954_);
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_k_1897_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_v_1898_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v_r_1900_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_size_1977_ = lean_ctor_get(v_l_1890_, 0);
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v___x_1978_, v_size_1977_);
v___x_1980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v_k_1888_);
lean_ctor_set(v___x_1980_, 2, v_v_1889_);
lean_ctor_set(v___x_1980_, 3, v_l_1890_);
lean_ctor_set(v___x_1980_, 4, v_r_1891_);
return v___x_1980_;
}
}
else
{
if (lean_obj_tag(v_r_1891_) == 0)
{
lean_object* v_l_1981_; 
v_l_1981_ = lean_ctor_get(v_r_1891_, 3);
lean_inc(v_l_1981_);
if (lean_obj_tag(v_l_1981_) == 0)
{
lean_object* v_r_1982_; 
v_r_1982_ = lean_ctor_get(v_r_1891_, 4);
lean_inc(v_r_1982_);
if (lean_obj_tag(v_r_1982_) == 0)
{
lean_object* v_size_1983_; lean_object* v_k_1984_; lean_object* v_v_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1997_; 
v_size_1983_ = lean_ctor_get(v_r_1891_, 0);
v_k_1984_ = lean_ctor_get(v_r_1891_, 1);
v_v_1985_ = lean_ctor_get(v_r_1891_, 2);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_r_1891_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; lean_object* v_unused_1999_; 
v_unused_1998_ = lean_ctor_get(v_r_1891_, 4);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_r_1891_, 3);
lean_dec(v_unused_1999_);
v___x_1987_ = v_r_1891_;
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_v_1985_);
lean_inc(v_k_1984_);
lean_inc(v_size_1983_);
lean_dec(v_r_1891_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_size_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v_size_1989_ = lean_ctor_get(v_l_1981_, 0);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_add(v___x_1990_, v_size_1983_);
lean_dec(v_size_1983_);
v___x_1992_ = lean_nat_add(v___x_1990_, v_size_1989_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_l_1981_);
lean_ctor_set(v___x_1987_, 3, v_l_1890_);
lean_ctor_set(v___x_1987_, 2, v_v_1889_);
lean_ctor_set(v___x_1987_, 1, v_k_1888_);
lean_ctor_set(v___x_1987_, 0, v___x_1992_);
v___x_1994_ = v___x_1987_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_k_1888_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_v_1889_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_l_1890_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_l_1981_);
v___x_1994_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1991_);
lean_ctor_set(v___x_1995_, 1, v_k_1984_);
lean_ctor_set(v___x_1995_, 2, v_v_1985_);
lean_ctor_set(v___x_1995_, 3, v___x_1994_);
lean_ctor_set(v___x_1995_, 4, v_r_1982_);
return v___x_1995_;
}
}
}
else
{
lean_object* v_k_2000_; lean_object* v_v_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2023_; 
v_k_2000_ = lean_ctor_get(v_r_1891_, 1);
v_v_2001_ = lean_ctor_get(v_r_1891_, 2);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_r_1891_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; lean_object* v_unused_2025_; lean_object* v_unused_2026_; 
v_unused_2024_ = lean_ctor_get(v_r_1891_, 4);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_r_1891_, 3);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_r_1891_, 0);
lean_dec(v_unused_2026_);
v___x_2003_ = v_r_1891_;
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_v_2001_);
lean_inc(v_k_2000_);
lean_dec(v_r_1891_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_k_2005_; lean_object* v_v_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2019_; 
v_k_2005_ = lean_ctor_get(v_l_1981_, 1);
v_v_2006_ = lean_ctor_get(v_l_1981_, 2);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_l_1981_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; 
v_unused_2020_ = lean_ctor_get(v_l_1981_, 4);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_l_1981_, 3);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_l_1981_, 0);
lean_dec(v_unused_2022_);
v___x_2008_ = v_l_1981_;
v_isShared_2009_ = v_isSharedCheck_2019_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_v_2006_);
lean_inc(v_k_2005_);
lean_dec(v_l_1981_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2019_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2010_ = lean_unsigned_to_nat(3u);
v___x_2011_ = lean_unsigned_to_nat(1u);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v_r_1982_);
lean_ctor_set(v___x_2008_, 3, v_r_1982_);
lean_ctor_set(v___x_2008_, 2, v_v_1889_);
lean_ctor_set(v___x_2008_, 1, v_k_1888_);
lean_ctor_set(v___x_2008_, 0, v___x_2011_);
v___x_2013_ = v___x_2008_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_k_1888_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_v_1889_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_r_1982_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_r_1982_);
v___x_2013_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 3, v_r_1982_);
lean_ctor_set(v___x_2003_, 0, v___x_2011_);
v___x_2015_ = v___x_2003_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_k_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_v_2001_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_r_1982_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_r_1982_);
v___x_2015_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2010_);
lean_ctor_set(v___x_2016_, 1, v_k_2005_);
lean_ctor_set(v___x_2016_, 2, v_v_2006_);
lean_ctor_set(v___x_2016_, 3, v___x_2013_);
lean_ctor_set(v___x_2016_, 4, v___x_2015_);
return v___x_2016_;
}
}
}
}
}
}
else
{
lean_object* v_r_2027_; 
v_r_2027_ = lean_ctor_get(v_r_1891_, 4);
lean_inc(v_r_2027_);
if (lean_obj_tag(v_r_2027_) == 0)
{
lean_object* v_k_2028_; lean_object* v_v_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_k_2028_ = lean_ctor_get(v_r_1891_, 1);
v_v_2029_ = lean_ctor_get(v_r_1891_, 2);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_r_1891_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; lean_object* v_unused_2041_; lean_object* v_unused_2042_; 
v_unused_2040_ = lean_ctor_get(v_r_1891_, 4);
lean_dec(v_unused_2040_);
v_unused_2041_ = lean_ctor_get(v_r_1891_, 3);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_r_1891_, 0);
lean_dec(v_unused_2042_);
v___x_2031_ = v_r_1891_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_v_2029_);
lean_inc(v_k_2028_);
lean_dec(v_r_1891_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2033_ = lean_unsigned_to_nat(3u);
v___x_2034_ = lean_unsigned_to_nat(1u);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 4, v_l_1981_);
lean_ctor_set(v___x_2031_, 2, v_v_1889_);
lean_ctor_set(v___x_2031_, 1, v_k_1888_);
lean_ctor_set(v___x_2031_, 0, v___x_2034_);
v___x_2036_ = v___x_2031_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_k_1888_);
lean_ctor_set(v_reuseFailAlloc_2038_, 2, v_v_1889_);
lean_ctor_set(v_reuseFailAlloc_2038_, 3, v_l_1981_);
lean_ctor_set(v_reuseFailAlloc_2038_, 4, v_l_1981_);
v___x_2036_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2033_);
lean_ctor_set(v___x_2037_, 1, v_k_2028_);
lean_ctor_set(v___x_2037_, 2, v_v_2029_);
lean_ctor_set(v___x_2037_, 3, v___x_2036_);
lean_ctor_set(v___x_2037_, 4, v_r_2027_);
return v___x_2037_;
}
}
}
else
{
lean_object* v_size_2043_; lean_object* v_k_2044_; lean_object* v_v_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2054_; 
v_size_2043_ = lean_ctor_get(v_r_1891_, 0);
v_k_2044_ = lean_ctor_get(v_r_1891_, 1);
v_v_2045_ = lean_ctor_get(v_r_1891_, 2);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_r_1891_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2055_ = lean_ctor_get(v_r_1891_, 4);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_r_1891_, 3);
lean_dec(v_unused_2056_);
v___x_2047_ = v_r_1891_;
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_v_2045_);
lean_inc(v_k_2044_);
lean_inc(v_size_2043_);
lean_dec(v_r_1891_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 3, v_r_2027_);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_size_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_k_2044_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_v_2045_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_r_2027_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_r_2027_);
v___x_2050_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_unsigned_to_nat(2u);
v___x_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v_k_1888_);
lean_ctor_set(v___x_2052_, 2, v_v_1889_);
lean_ctor_set(v___x_2052_, 3, v_r_2027_);
lean_ctor_set(v___x_2052_, 4, v___x_2050_);
return v___x_2052_;
}
}
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v_k_1888_);
lean_ctor_set(v___x_2058_, 2, v_v_1889_);
lean_ctor_set(v___x_2058_, 3, v_r_1891_);
lean_ctor_set(v___x_2058_, 4, v_r_1891_);
return v___x_2058_;
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2061_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
v___x_2062_ = lean_unsigned_to_nat(35u);
v___x_2063_ = lean_unsigned_to_nat(276u);
v___x_2064_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
v___x_2065_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2066_ = l_mkPanicMessageWithDecl(v___x_2065_, v___x_2064_, v___x_2063_, v___x_2062_, v___x_2061_);
return v___x_2066_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2067_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
v___x_2068_ = lean_unsigned_to_nat(21u);
v___x_2069_ = lean_unsigned_to_nat(277u);
v___x_2070_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
v___x_2071_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2072_ = l_mkPanicMessageWithDecl(v___x_2071_, v___x_2070_, v___x_2069_, v___x_2068_, v___x_2067_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg(lean_object* v_k_2073_, lean_object* v_v_2074_, lean_object* v_l_2075_, lean_object* v_r_2076_){
_start:
{
if (lean_obj_tag(v_l_2075_) == 0)
{
if (lean_obj_tag(v_r_2076_) == 0)
{
lean_object* v_size_2077_; lean_object* v_size_2078_; lean_object* v_k_2079_; lean_object* v_v_2080_; lean_object* v_l_2081_; lean_object* v_r_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_size_2077_ = lean_ctor_get(v_l_2075_, 0);
v_size_2078_ = lean_ctor_get(v_r_2076_, 0);
v_k_2079_ = lean_ctor_get(v_r_2076_, 1);
v_v_2080_ = lean_ctor_get(v_r_2076_, 2);
v_l_2081_ = lean_ctor_get(v_r_2076_, 3);
lean_inc(v_l_2081_);
v_r_2082_ = lean_ctor_get(v_r_2076_, 4);
v___x_2083_ = lean_unsigned_to_nat(3u);
v___x_2084_ = lean_nat_mul(v___x_2083_, v_size_2077_);
v___x_2085_ = lean_nat_dec_lt(v___x_2084_, v_size_2078_);
lean_dec(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec(v_l_2081_);
v___x_2086_ = lean_unsigned_to_nat(1u);
v___x_2087_ = lean_nat_add(v___x_2086_, v_size_2077_);
v___x_2088_ = lean_nat_add(v___x_2087_, v_size_2078_);
lean_dec(v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v_k_2073_);
lean_ctor_set(v___x_2089_, 2, v_v_2074_);
lean_ctor_set(v___x_2089_, 3, v_l_2075_);
lean_ctor_set(v___x_2089_, 4, v_r_2076_);
return v___x_2089_;
}
else
{
lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2159_; 
lean_inc(v_r_2082_);
lean_inc(v_v_2080_);
lean_inc(v_k_2079_);
lean_inc(v_size_2078_);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; lean_object* v_unused_2161_; lean_object* v_unused_2162_; lean_object* v_unused_2163_; lean_object* v_unused_2164_; 
v_unused_2160_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_r_2076_, 2);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_r_2076_, 1);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2164_);
v___x_2091_ = v_r_2076_;
v_isShared_2092_ = v_isSharedCheck_2159_;
goto v_resetjp_2090_;
}
else
{
lean_dec(v_r_2076_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2159_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
if (lean_obj_tag(v_l_2081_) == 0)
{
if (lean_obj_tag(v_r_2082_) == 0)
{
lean_object* v_size_2093_; lean_object* v_k_2094_; lean_object* v_v_2095_; lean_object* v_l_2096_; lean_object* v_r_2097_; lean_object* v_size_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_size_2093_ = lean_ctor_get(v_l_2081_, 0);
v_k_2094_ = lean_ctor_get(v_l_2081_, 1);
v_v_2095_ = lean_ctor_get(v_l_2081_, 2);
v_l_2096_ = lean_ctor_get(v_l_2081_, 3);
v_r_2097_ = lean_ctor_get(v_l_2081_, 4);
v_size_2098_ = lean_ctor_get(v_r_2082_, 0);
v___x_2099_ = lean_unsigned_to_nat(2u);
v___x_2100_ = lean_nat_mul(v___x_2099_, v_size_2098_);
v___x_2101_ = lean_nat_dec_lt(v_size_2093_, v___x_2100_);
lean_dec(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2128_; 
lean_inc(v_r_2097_);
lean_inc(v_l_2096_);
lean_inc(v_v_2095_);
lean_inc(v_k_2094_);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_l_2081_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; 
v_unused_2129_ = lean_ctor_get(v_l_2081_, 4);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_l_2081_, 3);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_l_2081_, 2);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_2081_, 1);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_l_2081_, 0);
lean_dec(v_unused_2133_);
v___x_2103_ = v_l_2081_;
v_isShared_2104_ = v_isSharedCheck_2128_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v_l_2081_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2128_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2120_; 
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_add(v___x_2105_, v_size_2077_);
v___x_2107_ = lean_nat_add(v___x_2106_, v_size_2078_);
lean_dec(v_size_2078_);
if (lean_obj_tag(v_l_2096_) == 0)
{
lean_object* v_size_2126_; 
v_size_2126_ = lean_ctor_get(v_l_2096_, 0);
lean_inc(v_size_2126_);
v___y_2120_ = v_size_2126_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___y_2120_ = v___x_2127_;
goto v___jp_2119_;
}
v___jp_2108_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = lean_nat_add(v___y_2109_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec(v___y_2109_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v_r_2082_);
lean_ctor_set(v___x_2103_, 3, v_r_2097_);
lean_ctor_set(v___x_2103_, 2, v_v_2080_);
lean_ctor_set(v___x_2103_, 1, v_k_2079_);
lean_ctor_set(v___x_2103_, 0, v___x_2112_);
v___x_2114_ = v___x_2103_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_r_2097_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_r_2082_);
v___x_2114_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v___x_2114_);
lean_ctor_set(v___x_2091_, 3, v___y_2110_);
lean_ctor_set(v___x_2091_, 2, v_v_2095_);
lean_ctor_set(v___x_2091_, 1, v_k_2094_);
lean_ctor_set(v___x_2091_, 0, v___x_2107_);
v___x_2116_ = v___x_2091_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v___y_2110_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
v___jp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_nat_add(v___x_2106_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec(v___x_2106_);
v___x_2122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v_k_2073_);
lean_ctor_set(v___x_2122_, 2, v_v_2074_);
lean_ctor_set(v___x_2122_, 3, v_l_2075_);
lean_ctor_set(v___x_2122_, 4, v_l_2096_);
v___x_2123_ = lean_nat_add(v___x_2105_, v_size_2098_);
if (lean_obj_tag(v_r_2097_) == 0)
{
lean_object* v_size_2124_; 
v_size_2124_ = lean_ctor_get(v_r_2097_, 0);
lean_inc(v_size_2124_);
v___y_2109_ = v___x_2123_;
v___y_2110_ = v___x_2122_;
v___y_2111_ = v_size_2124_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___y_2109_ = v___x_2123_;
v___y_2110_ = v___x_2122_;
v___y_2111_ = v___x_2125_;
goto v___jp_2108_;
}
}
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2134_ = lean_unsigned_to_nat(1u);
v___x_2135_ = lean_nat_add(v___x_2134_, v_size_2077_);
v___x_2136_ = lean_nat_add(v___x_2135_, v_size_2078_);
lean_dec(v_size_2078_);
v___x_2137_ = lean_nat_add(v___x_2135_, v_size_2093_);
lean_dec(v___x_2135_);
lean_inc_ref(v_l_2075_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v_l_2081_);
lean_ctor_set(v___x_2091_, 3, v_l_2075_);
lean_ctor_set(v___x_2091_, 2, v_v_2074_);
lean_ctor_set(v___x_2091_, 1, v_k_2073_);
lean_ctor_set(v___x_2091_, 0, v___x_2137_);
v___x_2139_ = v___x_2091_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_l_2075_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_l_2081_);
v___x_2139_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; 
v_unused_2147_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2075_, 2);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2075_, 1);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2151_);
v___x_2141_ = v_l_2075_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_l_2075_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v_r_2082_);
lean_ctor_set(v___x_2141_, 3, v___x_2139_);
lean_ctor_set(v___x_2141_, 2, v_v_2080_);
lean_ctor_set(v___x_2141_, 1, v_k_2079_);
lean_ctor_set(v___x_2141_, 0, v___x_2136_);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_r_2082_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v_l_2081_);
lean_del_object(v___x_2091_);
lean_dec(v_v_2080_);
lean_dec(v_k_2079_);
lean_dec(v_size_2078_);
lean_dec_ref(v_l_2075_);
lean_dec(v_v_2074_);
lean_dec(v_k_2073_);
v___x_2153_ = lean_box(1);
v___x_2154_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
v___x_2155_ = l_panic___redArg(v___x_2153_, v___x_2154_);
return v___x_2155_;
}
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_del_object(v___x_2091_);
lean_dec(v_r_2082_);
lean_dec(v_v_2080_);
lean_dec(v_k_2079_);
lean_dec(v_size_2078_);
lean_dec_ref(v_l_2075_);
lean_dec(v_v_2074_);
lean_dec(v_k_2073_);
v___x_2156_ = lean_box(1);
v___x_2157_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
v___x_2158_ = l_panic___redArg(v___x_2156_, v___x_2157_);
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_size_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_size_2165_ = lean_ctor_get(v_l_2075_, 0);
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_add(v___x_2166_, v_size_2165_);
v___x_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v_k_2073_);
lean_ctor_set(v___x_2168_, 2, v_v_2074_);
lean_ctor_set(v___x_2168_, 3, v_l_2075_);
lean_ctor_set(v___x_2168_, 4, v_r_2076_);
return v___x_2168_;
}
}
else
{
if (lean_obj_tag(v_r_2076_) == 0)
{
lean_object* v_l_2169_; 
v_l_2169_ = lean_ctor_get(v_r_2076_, 3);
lean_inc(v_l_2169_);
if (lean_obj_tag(v_l_2169_) == 0)
{
lean_object* v_r_2170_; 
v_r_2170_ = lean_ctor_get(v_r_2076_, 4);
lean_inc(v_r_2170_);
if (lean_obj_tag(v_r_2170_) == 0)
{
lean_object* v_size_2171_; lean_object* v_k_2172_; lean_object* v_v_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2185_; 
v_size_2171_ = lean_ctor_get(v_r_2076_, 0);
v_k_2172_ = lean_ctor_get(v_r_2076_, 1);
v_v_2173_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; lean_object* v_unused_2187_; 
v_unused_2186_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2187_);
v___x_2175_ = v_r_2076_;
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_v_2173_);
lean_inc(v_k_2172_);
lean_inc(v_size_2171_);
lean_dec(v_r_2076_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_size_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v_size_2177_ = lean_ctor_get(v_l_2169_, 0);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v___x_2178_, v_size_2171_);
lean_dec(v_size_2171_);
v___x_2180_ = lean_nat_add(v___x_2178_, v_size_2177_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 4, v_l_2169_);
lean_ctor_set(v___x_2175_, 3, v_l_2075_);
lean_ctor_set(v___x_2175_, 2, v_v_2074_);
lean_ctor_set(v___x_2175_, 1, v_k_2073_);
lean_ctor_set(v___x_2175_, 0, v___x_2180_);
v___x_2182_ = v___x_2175_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2184_, 3, v_l_2075_);
lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_l_2169_);
v___x_2182_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2179_);
lean_ctor_set(v___x_2183_, 1, v_k_2172_);
lean_ctor_set(v___x_2183_, 2, v_v_2173_);
lean_ctor_set(v___x_2183_, 3, v___x_2182_);
lean_ctor_set(v___x_2183_, 4, v_r_2170_);
return v___x_2183_;
}
}
}
else
{
lean_object* v_k_2188_; lean_object* v_v_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2211_; 
v_k_2188_ = lean_ctor_get(v_r_2076_, 1);
v_v_2189_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; 
v_unused_2212_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2214_);
v___x_2191_ = v_r_2076_;
v_isShared_2192_ = v_isSharedCheck_2211_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_v_2189_);
lean_inc(v_k_2188_);
lean_dec(v_r_2076_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2211_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v_k_2193_; lean_object* v_v_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2207_; 
v_k_2193_ = lean_ctor_get(v_l_2169_, 1);
v_v_2194_ = lean_ctor_get(v_l_2169_, 2);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_l_2169_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2208_ = lean_ctor_get(v_l_2169_, 4);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_l_2169_, 3);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_l_2169_, 0);
lean_dec(v_unused_2210_);
v___x_2196_ = v_l_2169_;
v_isShared_2197_ = v_isSharedCheck_2207_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_v_2194_);
lean_inc(v_k_2193_);
lean_dec(v_l_2169_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2207_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2198_ = lean_unsigned_to_nat(3u);
v___x_2199_ = lean_unsigned_to_nat(1u);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v_r_2170_);
lean_ctor_set(v___x_2196_, 3, v_r_2170_);
lean_ctor_set(v___x_2196_, 2, v_v_2074_);
lean_ctor_set(v___x_2196_, 1, v_k_2073_);
lean_ctor_set(v___x_2196_, 0, v___x_2199_);
v___x_2201_ = v___x_2196_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_r_2170_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_r_2170_);
v___x_2201_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 3, v_r_2170_);
lean_ctor_set(v___x_2191_, 0, v___x_2199_);
v___x_2203_ = v___x_2191_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_k_2188_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_v_2189_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_r_2170_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_r_2170_);
v___x_2203_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2198_);
lean_ctor_set(v___x_2204_, 1, v_k_2193_);
lean_ctor_set(v___x_2204_, 2, v_v_2194_);
lean_ctor_set(v___x_2204_, 3, v___x_2201_);
lean_ctor_set(v___x_2204_, 4, v___x_2203_);
return v___x_2204_;
}
}
}
}
}
}
else
{
lean_object* v_r_2215_; 
v_r_2215_ = lean_ctor_get(v_r_2076_, 4);
lean_inc(v_r_2215_);
if (lean_obj_tag(v_r_2215_) == 0)
{
lean_object* v_k_2216_; lean_object* v_v_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2227_; 
v_k_2216_ = lean_ctor_get(v_r_2076_, 1);
v_v_2217_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; lean_object* v_unused_2230_; 
v_unused_2228_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2230_);
v___x_2219_ = v_r_2076_;
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_v_2217_);
lean_inc(v_k_2216_);
lean_dec(v_r_2076_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2221_ = lean_unsigned_to_nat(3u);
v___x_2222_ = lean_unsigned_to_nat(1u);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 4, v_l_2169_);
lean_ctor_set(v___x_2219_, 2, v_v_2074_);
lean_ctor_set(v___x_2219_, 1, v_k_2073_);
lean_ctor_set(v___x_2219_, 0, v___x_2222_);
v___x_2224_ = v___x_2219_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_l_2169_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_l_2169_);
v___x_2224_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2221_);
lean_ctor_set(v___x_2225_, 1, v_k_2216_);
lean_ctor_set(v___x_2225_, 2, v_v_2217_);
lean_ctor_set(v___x_2225_, 3, v___x_2224_);
lean_ctor_set(v___x_2225_, 4, v_r_2215_);
return v___x_2225_;
}
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_unsigned_to_nat(2u);
v___x_2232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v_k_2073_);
lean_ctor_set(v___x_2232_, 2, v_v_2074_);
lean_ctor_set(v___x_2232_, 3, v_r_2215_);
lean_ctor_set(v___x_2232_, 4, v_r_2076_);
return v___x_2232_;
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v_k_2073_);
lean_ctor_set(v___x_2234_, 2, v_v_2074_);
lean_ctor_set(v___x_2234_, 3, v_r_2076_);
lean_ctor_set(v___x_2234_, 4, v_r_2076_);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21(lean_object* v_00_u03b1_2235_, lean_object* v_00_u03b2_2236_, lean_object* v_k_2237_, lean_object* v_v_2238_, lean_object* v_l_2239_, lean_object* v_r_2240_){
_start:
{
if (lean_obj_tag(v_l_2239_) == 0)
{
if (lean_obj_tag(v_r_2240_) == 0)
{
lean_object* v_size_2241_; lean_object* v_size_2242_; lean_object* v_k_2243_; lean_object* v_v_2244_; lean_object* v_l_2245_; lean_object* v_r_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v_size_2241_ = lean_ctor_get(v_l_2239_, 0);
v_size_2242_ = lean_ctor_get(v_r_2240_, 0);
v_k_2243_ = lean_ctor_get(v_r_2240_, 1);
v_v_2244_ = lean_ctor_get(v_r_2240_, 2);
v_l_2245_ = lean_ctor_get(v_r_2240_, 3);
lean_inc(v_l_2245_);
v_r_2246_ = lean_ctor_get(v_r_2240_, 4);
v___x_2247_ = lean_unsigned_to_nat(3u);
v___x_2248_ = lean_nat_mul(v___x_2247_, v_size_2241_);
v___x_2249_ = lean_nat_dec_lt(v___x_2248_, v_size_2242_);
lean_dec(v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v_l_2245_);
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_add(v___x_2250_, v_size_2241_);
v___x_2252_ = lean_nat_add(v___x_2251_, v_size_2242_);
lean_dec(v___x_2251_);
v___x_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v_k_2237_);
lean_ctor_set(v___x_2253_, 2, v_v_2238_);
lean_ctor_set(v___x_2253_, 3, v_l_2239_);
lean_ctor_set(v___x_2253_, 4, v_r_2240_);
return v___x_2253_;
}
else
{
lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2323_; 
lean_inc(v_r_2246_);
lean_inc(v_v_2244_);
lean_inc(v_k_2243_);
lean_inc(v_size_2242_);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_r_2240_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; lean_object* v_unused_2325_; lean_object* v_unused_2326_; lean_object* v_unused_2327_; lean_object* v_unused_2328_; 
v_unused_2324_ = lean_ctor_get(v_r_2240_, 4);
lean_dec(v_unused_2324_);
v_unused_2325_ = lean_ctor_get(v_r_2240_, 3);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_r_2240_, 2);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_r_2240_, 1);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_r_2240_, 0);
lean_dec(v_unused_2328_);
v___x_2255_ = v_r_2240_;
v_isShared_2256_ = v_isSharedCheck_2323_;
goto v_resetjp_2254_;
}
else
{
lean_dec(v_r_2240_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2323_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
if (lean_obj_tag(v_l_2245_) == 0)
{
if (lean_obj_tag(v_r_2246_) == 0)
{
lean_object* v_size_2257_; lean_object* v_k_2258_; lean_object* v_v_2259_; lean_object* v_l_2260_; lean_object* v_r_2261_; lean_object* v_size_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v_size_2257_ = lean_ctor_get(v_l_2245_, 0);
v_k_2258_ = lean_ctor_get(v_l_2245_, 1);
v_v_2259_ = lean_ctor_get(v_l_2245_, 2);
v_l_2260_ = lean_ctor_get(v_l_2245_, 3);
v_r_2261_ = lean_ctor_get(v_l_2245_, 4);
v_size_2262_ = lean_ctor_get(v_r_2246_, 0);
v___x_2263_ = lean_unsigned_to_nat(2u);
v___x_2264_ = lean_nat_mul(v___x_2263_, v_size_2262_);
v___x_2265_ = lean_nat_dec_lt(v_size_2257_, v___x_2264_);
lean_dec(v___x_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2292_; 
lean_inc(v_r_2261_);
lean_inc(v_l_2260_);
lean_inc(v_v_2259_);
lean_inc(v_k_2258_);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_l_2245_);
if (v_isSharedCheck_2292_ == 0)
{
lean_object* v_unused_2293_; lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; lean_object* v_unused_2297_; 
v_unused_2293_ = lean_ctor_get(v_l_2245_, 4);
lean_dec(v_unused_2293_);
v_unused_2294_ = lean_ctor_get(v_l_2245_, 3);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_l_2245_, 2);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_l_2245_, 1);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_l_2245_, 0);
lean_dec(v_unused_2297_);
v___x_2267_ = v_l_2245_;
v_isShared_2268_ = v_isSharedCheck_2292_;
goto v_resetjp_2266_;
}
else
{
lean_dec(v_l_2245_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2292_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2284_; 
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_add(v___x_2269_, v_size_2241_);
v___x_2271_ = lean_nat_add(v___x_2270_, v_size_2242_);
lean_dec(v_size_2242_);
if (lean_obj_tag(v_l_2260_) == 0)
{
lean_object* v_size_2290_; 
v_size_2290_ = lean_ctor_get(v_l_2260_, 0);
lean_inc(v_size_2290_);
v___y_2284_ = v_size_2290_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___y_2284_ = v___x_2291_;
goto v___jp_2283_;
}
v___jp_2272_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_nat_add(v___y_2273_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec(v___y_2273_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_r_2246_);
lean_ctor_set(v___x_2267_, 3, v_r_2261_);
lean_ctor_set(v___x_2267_, 2, v_v_2244_);
lean_ctor_set(v___x_2267_, 1, v_k_2243_);
lean_ctor_set(v___x_2267_, 0, v___x_2276_);
v___x_2278_ = v___x_2267_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_2243_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_2244_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_r_2261_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_r_2246_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 4, v___x_2278_);
lean_ctor_set(v___x_2255_, 3, v___y_2274_);
lean_ctor_set(v___x_2255_, 2, v_v_2259_);
lean_ctor_set(v___x_2255_, 1, v_k_2258_);
lean_ctor_set(v___x_2255_, 0, v___x_2271_);
v___x_2280_ = v___x_2255_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_k_2258_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_v_2259_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v___y_2274_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
v___jp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_nat_add(v___x_2270_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec(v___x_2270_);
v___x_2286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v_k_2237_);
lean_ctor_set(v___x_2286_, 2, v_v_2238_);
lean_ctor_set(v___x_2286_, 3, v_l_2239_);
lean_ctor_set(v___x_2286_, 4, v_l_2260_);
v___x_2287_ = lean_nat_add(v___x_2269_, v_size_2262_);
if (lean_obj_tag(v_r_2261_) == 0)
{
lean_object* v_size_2288_; 
v_size_2288_ = lean_ctor_get(v_r_2261_, 0);
lean_inc(v_size_2288_);
v___y_2273_ = v___x_2287_;
v___y_2274_ = v___x_2286_;
v___y_2275_ = v_size_2288_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_unsigned_to_nat(0u);
v___y_2273_ = v___x_2287_;
v___y_2274_ = v___x_2286_;
v___y_2275_ = v___x_2289_;
goto v___jp_2272_;
}
}
}
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_add(v___x_2298_, v_size_2241_);
v___x_2300_ = lean_nat_add(v___x_2299_, v_size_2242_);
lean_dec(v_size_2242_);
v___x_2301_ = lean_nat_add(v___x_2299_, v_size_2257_);
lean_dec(v___x_2299_);
lean_inc_ref(v_l_2239_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 4, v_l_2245_);
lean_ctor_set(v___x_2255_, 3, v_l_2239_);
lean_ctor_set(v___x_2255_, 2, v_v_2238_);
lean_ctor_set(v___x_2255_, 1, v_k_2237_);
lean_ctor_set(v___x_2255_, 0, v___x_2301_);
v___x_2303_ = v___x_2255_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_k_2237_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_v_2238_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v_l_2239_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v_l_2245_);
v___x_2303_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v_isSharedCheck_2310_ = !lean_is_exclusive(v_l_2239_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2311_ = lean_ctor_get(v_l_2239_, 4);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_l_2239_, 3);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_l_2239_, 2);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_l_2239_, 1);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_l_2239_, 0);
lean_dec(v_unused_2315_);
v___x_2305_ = v_l_2239_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v_l_2239_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_r_2246_);
lean_ctor_set(v___x_2305_, 3, v___x_2303_);
lean_ctor_set(v___x_2305_, 2, v_v_2244_);
lean_ctor_set(v___x_2305_, 1, v_k_2243_);
lean_ctor_set(v___x_2305_, 0, v___x_2300_);
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2243_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2244_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_r_2246_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec_ref(v_l_2245_);
lean_del_object(v___x_2255_);
lean_dec(v_v_2244_);
lean_dec(v_k_2243_);
lean_dec(v_size_2242_);
lean_dec_ref(v_l_2239_);
lean_dec(v_v_2238_);
lean_dec(v_k_2237_);
v___x_2317_ = lean_box(1);
v___x_2318_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
v___x_2319_ = l_panic___redArg(v___x_2317_, v___x_2318_);
return v___x_2319_;
}
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_del_object(v___x_2255_);
lean_dec(v_r_2246_);
lean_dec(v_v_2244_);
lean_dec(v_k_2243_);
lean_dec(v_size_2242_);
lean_dec_ref(v_l_2239_);
lean_dec(v_v_2238_);
lean_dec(v_k_2237_);
v___x_2320_ = lean_box(1);
v___x_2321_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
v___x_2322_ = l_panic___redArg(v___x_2320_, v___x_2321_);
return v___x_2322_;
}
}
}
}
else
{
lean_object* v_size_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_size_2329_ = lean_ctor_get(v_l_2239_, 0);
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v___x_2330_, v_size_2329_);
v___x_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v_k_2237_);
lean_ctor_set(v___x_2332_, 2, v_v_2238_);
lean_ctor_set(v___x_2332_, 3, v_l_2239_);
lean_ctor_set(v___x_2332_, 4, v_r_2240_);
return v___x_2332_;
}
}
else
{
if (lean_obj_tag(v_r_2240_) == 0)
{
lean_object* v_l_2333_; 
v_l_2333_ = lean_ctor_get(v_r_2240_, 3);
lean_inc(v_l_2333_);
if (lean_obj_tag(v_l_2333_) == 0)
{
lean_object* v_r_2334_; 
v_r_2334_ = lean_ctor_get(v_r_2240_, 4);
lean_inc(v_r_2334_);
if (lean_obj_tag(v_r_2334_) == 0)
{
lean_object* v_size_2335_; lean_object* v_k_2336_; lean_object* v_v_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2349_; 
v_size_2335_ = lean_ctor_get(v_r_2240_, 0);
v_k_2336_ = lean_ctor_get(v_r_2240_, 1);
v_v_2337_ = lean_ctor_get(v_r_2240_, 2);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_r_2240_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; lean_object* v_unused_2351_; 
v_unused_2350_ = lean_ctor_get(v_r_2240_, 4);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_r_2240_, 3);
lean_dec(v_unused_2351_);
v___x_2339_ = v_r_2240_;
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_v_2337_);
lean_inc(v_k_2336_);
lean_inc(v_size_2335_);
lean_dec(v_r_2240_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_size_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v_size_2341_ = lean_ctor_get(v_l_2333_, 0);
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = lean_nat_add(v___x_2342_, v_size_2335_);
lean_dec(v_size_2335_);
v___x_2344_ = lean_nat_add(v___x_2342_, v_size_2341_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 4, v_l_2333_);
lean_ctor_set(v___x_2339_, 3, v_l_2239_);
lean_ctor_set(v___x_2339_, 2, v_v_2238_);
lean_ctor_set(v___x_2339_, 1, v_k_2237_);
lean_ctor_set(v___x_2339_, 0, v___x_2344_);
v___x_2346_ = v___x_2339_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_2237_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_2238_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_l_2239_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_l_2333_);
v___x_2346_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2343_);
lean_ctor_set(v___x_2347_, 1, v_k_2336_);
lean_ctor_set(v___x_2347_, 2, v_v_2337_);
lean_ctor_set(v___x_2347_, 3, v___x_2346_);
lean_ctor_set(v___x_2347_, 4, v_r_2334_);
return v___x_2347_;
}
}
}
else
{
lean_object* v_k_2352_; lean_object* v_v_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2375_; 
v_k_2352_ = lean_ctor_get(v_r_2240_, 1);
v_v_2353_ = lean_ctor_get(v_r_2240_, 2);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_r_2240_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; lean_object* v_unused_2377_; lean_object* v_unused_2378_; 
v_unused_2376_ = lean_ctor_get(v_r_2240_, 4);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_r_2240_, 3);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_r_2240_, 0);
lean_dec(v_unused_2378_);
v___x_2355_ = v_r_2240_;
v_isShared_2356_ = v_isSharedCheck_2375_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_v_2353_);
lean_inc(v_k_2352_);
lean_dec(v_r_2240_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2375_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2371_; 
v_k_2357_ = lean_ctor_get(v_l_2333_, 1);
v_v_2358_ = lean_ctor_get(v_l_2333_, 2);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_l_2333_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; lean_object* v_unused_2373_; lean_object* v_unused_2374_; 
v_unused_2372_ = lean_ctor_get(v_l_2333_, 4);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_l_2333_, 3);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_l_2333_, 0);
lean_dec(v_unused_2374_);
v___x_2360_ = v_l_2333_;
v_isShared_2361_ = v_isSharedCheck_2371_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_v_2358_);
lean_inc(v_k_2357_);
lean_dec(v_l_2333_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2371_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2362_ = lean_unsigned_to_nat(3u);
v___x_2363_ = lean_unsigned_to_nat(1u);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 4, v_r_2334_);
lean_ctor_set(v___x_2360_, 3, v_r_2334_);
lean_ctor_set(v___x_2360_, 2, v_v_2238_);
lean_ctor_set(v___x_2360_, 1, v_k_2237_);
lean_ctor_set(v___x_2360_, 0, v___x_2363_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_k_2237_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_v_2238_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_r_2334_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_r_2334_);
v___x_2365_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 3, v_r_2334_);
lean_ctor_set(v___x_2355_, 0, v___x_2363_);
v___x_2367_ = v___x_2355_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_k_2352_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_v_2353_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v_r_2334_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v_r_2334_);
v___x_2367_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2362_);
lean_ctor_set(v___x_2368_, 1, v_k_2357_);
lean_ctor_set(v___x_2368_, 2, v_v_2358_);
lean_ctor_set(v___x_2368_, 3, v___x_2365_);
lean_ctor_set(v___x_2368_, 4, v___x_2367_);
return v___x_2368_;
}
}
}
}
}
}
else
{
lean_object* v_r_2379_; 
v_r_2379_ = lean_ctor_get(v_r_2240_, 4);
lean_inc(v_r_2379_);
if (lean_obj_tag(v_r_2379_) == 0)
{
lean_object* v_k_2380_; lean_object* v_v_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2391_; 
v_k_2380_ = lean_ctor_get(v_r_2240_, 1);
v_v_2381_ = lean_ctor_get(v_r_2240_, 2);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_r_2240_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; lean_object* v_unused_2393_; lean_object* v_unused_2394_; 
v_unused_2392_ = lean_ctor_get(v_r_2240_, 4);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_r_2240_, 3);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_r_2240_, 0);
lean_dec(v_unused_2394_);
v___x_2383_ = v_r_2240_;
v_isShared_2384_ = v_isSharedCheck_2391_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_v_2381_);
lean_inc(v_k_2380_);
lean_dec(v_r_2240_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2391_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2385_ = lean_unsigned_to_nat(3u);
v___x_2386_ = lean_unsigned_to_nat(1u);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 4, v_l_2333_);
lean_ctor_set(v___x_2383_, 2, v_v_2238_);
lean_ctor_set(v___x_2383_, 1, v_k_2237_);
lean_ctor_set(v___x_2383_, 0, v___x_2386_);
v___x_2388_ = v___x_2383_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_k_2237_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v_v_2238_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v_l_2333_);
lean_ctor_set(v_reuseFailAlloc_2390_, 4, v_l_2333_);
v___x_2388_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2385_);
lean_ctor_set(v___x_2389_, 1, v_k_2380_);
lean_ctor_set(v___x_2389_, 2, v_v_2381_);
lean_ctor_set(v___x_2389_, 3, v___x_2388_);
lean_ctor_set(v___x_2389_, 4, v_r_2379_);
return v___x_2389_;
}
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_unsigned_to_nat(2u);
v___x_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v_k_2237_);
lean_ctor_set(v___x_2396_, 2, v_v_2238_);
lean_ctor_set(v___x_2396_, 3, v_r_2379_);
lean_ctor_set(v___x_2396_, 4, v_r_2240_);
return v___x_2396_;
}
}
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v_k_2237_);
lean_ctor_set(v___x_2398_, 2, v_v_2238_);
lean_ctor_set(v___x_2398_, 3, v_r_2240_);
lean_ctor_set(v___x_2398_, 4, v_r_2240_);
return v___x_2398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object* v_k_2399_, lean_object* v_v_2400_, lean_object* v_l_2401_, lean_object* v_r_2402_){
_start:
{
if (lean_obj_tag(v_l_2401_) == 0)
{
if (lean_obj_tag(v_r_2402_) == 0)
{
lean_object* v_size_2403_; lean_object* v_k_2404_; lean_object* v_v_2405_; lean_object* v_l_2406_; lean_object* v_r_2407_; lean_object* v_size_2408_; lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v_l_2411_; lean_object* v_r_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_size_2403_ = lean_ctor_get(v_l_2401_, 0);
v_k_2404_ = lean_ctor_get(v_l_2401_, 1);
v_v_2405_ = lean_ctor_get(v_l_2401_, 2);
v_l_2406_ = lean_ctor_get(v_l_2401_, 3);
v_r_2407_ = lean_ctor_get(v_l_2401_, 4);
lean_inc(v_r_2407_);
v_size_2408_ = lean_ctor_get(v_r_2402_, 0);
v_k_2409_ = lean_ctor_get(v_r_2402_, 1);
v_v_2410_ = lean_ctor_get(v_r_2402_, 2);
v_l_2411_ = lean_ctor_get(v_r_2402_, 3);
lean_inc(v_l_2411_);
v_r_2412_ = lean_ctor_get(v_r_2402_, 4);
v___x_2413_ = lean_unsigned_to_nat(3u);
v___x_2414_ = lean_nat_mul(v___x_2413_, v_size_2403_);
v___x_2415_ = lean_nat_dec_lt(v___x_2414_, v_size_2408_);
lean_dec(v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
lean_dec(v_l_2411_);
v___x_2416_ = lean_nat_mul(v___x_2413_, v_size_2408_);
v___x_2417_ = lean_nat_dec_lt(v___x_2416_, v_size_2403_);
lean_dec(v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec(v_r_2407_);
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_nat_add(v___x_2418_, v_size_2403_);
v___x_2420_ = lean_nat_add(v___x_2419_, v_size_2408_);
lean_dec(v___x_2419_);
v___x_2421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v_k_2399_);
lean_ctor_set(v___x_2421_, 2, v_v_2400_);
lean_ctor_set(v___x_2421_, 3, v_l_2401_);
lean_ctor_set(v___x_2421_, 4, v_r_2402_);
return v___x_2421_;
}
else
{
lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2487_; 
lean_inc(v_l_2406_);
lean_inc(v_v_2405_);
lean_inc(v_k_2404_);
lean_inc(v_size_2403_);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_l_2401_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; lean_object* v_unused_2489_; lean_object* v_unused_2490_; lean_object* v_unused_2491_; lean_object* v_unused_2492_; 
v_unused_2488_ = lean_ctor_get(v_l_2401_, 4);
lean_dec(v_unused_2488_);
v_unused_2489_ = lean_ctor_get(v_l_2401_, 3);
lean_dec(v_unused_2489_);
v_unused_2490_ = lean_ctor_get(v_l_2401_, 2);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_l_2401_, 1);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_l_2401_, 0);
lean_dec(v_unused_2492_);
v___x_2423_ = v_l_2401_;
v_isShared_2424_ = v_isSharedCheck_2487_;
goto v_resetjp_2422_;
}
else
{
lean_dec(v_l_2401_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2487_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_size_2425_; lean_object* v_size_2426_; lean_object* v_k_2427_; lean_object* v_v_2428_; lean_object* v_l_2429_; lean_object* v_r_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_size_2425_ = lean_ctor_get(v_l_2406_, 0);
v_size_2426_ = lean_ctor_get(v_r_2407_, 0);
v_k_2427_ = lean_ctor_get(v_r_2407_, 1);
v_v_2428_ = lean_ctor_get(v_r_2407_, 2);
v_l_2429_ = lean_ctor_get(v_r_2407_, 3);
v_r_2430_ = lean_ctor_get(v_r_2407_, 4);
v___x_2431_ = lean_unsigned_to_nat(2u);
v___x_2432_ = lean_nat_mul(v___x_2431_, v_size_2425_);
v___x_2433_ = lean_nat_dec_lt(v_size_2426_, v___x_2432_);
lean_dec(v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2472_; 
lean_inc(v_r_2430_);
lean_inc(v_l_2429_);
lean_inc(v_v_2428_);
lean_inc(v_k_2427_);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_r_2407_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; lean_object* v_unused_2474_; lean_object* v_unused_2475_; lean_object* v_unused_2476_; lean_object* v_unused_2477_; 
v_unused_2473_ = lean_ctor_get(v_r_2407_, 4);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_r_2407_, 3);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_r_2407_, 2);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_r_2407_, 1);
lean_dec(v_unused_2476_);
v_unused_2477_ = lean_ctor_get(v_r_2407_, 0);
lean_dec(v_unused_2477_);
v___x_2435_ = v_r_2407_;
v_isShared_2436_ = v_isSharedCheck_2472_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v_r_2407_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2472_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___x_2460_; lean_object* v___y_2462_; 
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2438_ = lean_nat_add(v___x_2437_, v_size_2403_);
lean_dec(v_size_2403_);
v___x_2439_ = lean_nat_add(v___x_2438_, v_size_2408_);
lean_dec(v___x_2438_);
v___x_2460_ = lean_nat_add(v___x_2437_, v_size_2425_);
if (lean_obj_tag(v_l_2429_) == 0)
{
lean_object* v_size_2470_; 
v_size_2470_ = lean_ctor_get(v_l_2429_, 0);
lean_inc(v_size_2470_);
v___y_2462_ = v_size_2470_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_unsigned_to_nat(0u);
v___y_2462_ = v___x_2471_;
goto v___jp_2461_;
}
v___jp_2440_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_nat_add(v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec(v___y_2442_);
lean_inc_ref(v_r_2402_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_r_2402_);
lean_ctor_set(v___x_2435_, 3, v_r_2430_);
lean_ctor_set(v___x_2435_, 2, v_v_2400_);
lean_ctor_set(v___x_2435_, 1, v_k_2399_);
lean_ctor_set(v___x_2435_, 0, v___x_2444_);
v___x_2446_ = v___x_2435_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_r_2430_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_r_2402_);
v___x_2446_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
v_isSharedCheck_2453_ = !lean_is_exclusive(v_r_2402_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; lean_object* v_unused_2455_; lean_object* v_unused_2456_; lean_object* v_unused_2457_; lean_object* v_unused_2458_; 
v_unused_2454_ = lean_ctor_get(v_r_2402_, 4);
lean_dec(v_unused_2454_);
v_unused_2455_ = lean_ctor_get(v_r_2402_, 3);
lean_dec(v_unused_2455_);
v_unused_2456_ = lean_ctor_get(v_r_2402_, 2);
lean_dec(v_unused_2456_);
v_unused_2457_ = lean_ctor_get(v_r_2402_, 1);
lean_dec(v_unused_2457_);
v_unused_2458_ = lean_ctor_get(v_r_2402_, 0);
lean_dec(v_unused_2458_);
v___x_2448_ = v_r_2402_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_dec(v_r_2402_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 4, v___x_2446_);
lean_ctor_set(v___x_2448_, 3, v___y_2441_);
lean_ctor_set(v___x_2448_, 2, v_v_2428_);
lean_ctor_set(v___x_2448_, 1, v_k_2427_);
lean_ctor_set(v___x_2448_, 0, v___x_2439_);
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v___y_2441_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v___x_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
v___jp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2463_ = lean_nat_add(v___x_2460_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec(v___x_2460_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 4, v_l_2429_);
lean_ctor_set(v___x_2423_, 0, v___x_2463_);
v___x_2465_ = v___x_2423_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_k_2404_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_v_2405_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_l_2406_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_l_2429_);
v___x_2465_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_nat_add(v___x_2437_, v_size_2408_);
if (lean_obj_tag(v_r_2430_) == 0)
{
lean_object* v_size_2467_; 
v_size_2467_ = lean_ctor_get(v_r_2430_, 0);
lean_inc(v_size_2467_);
v___y_2441_ = v___x_2465_;
v___y_2442_ = v___x_2466_;
v___y_2443_ = v_size_2467_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_unsigned_to_nat(0u);
v___y_2441_ = v___x_2465_;
v___y_2442_ = v___x_2466_;
v___y_2443_ = v___x_2468_;
goto v___jp_2440_;
}
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2478_ = lean_unsigned_to_nat(1u);
v___x_2479_ = lean_nat_add(v___x_2478_, v_size_2403_);
lean_dec(v_size_2403_);
v___x_2480_ = lean_nat_add(v___x_2479_, v_size_2408_);
lean_dec(v___x_2479_);
v___x_2481_ = lean_nat_add(v___x_2478_, v_size_2408_);
v___x_2482_ = lean_nat_add(v___x_2481_, v_size_2426_);
lean_dec(v___x_2481_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 4, v_r_2402_);
lean_ctor_set(v___x_2423_, 3, v_r_2407_);
lean_ctor_set(v___x_2423_, 2, v_v_2400_);
lean_ctor_set(v___x_2423_, 1, v_k_2399_);
lean_ctor_set(v___x_2423_, 0, v___x_2482_);
v___x_2484_ = v___x_2423_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_r_2407_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_r_2402_);
v___x_2484_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2480_);
lean_ctor_set(v___x_2485_, 1, v_k_2404_);
lean_ctor_set(v___x_2485_, 2, v_v_2405_);
lean_ctor_set(v___x_2485_, 3, v_l_2406_);
lean_ctor_set(v___x_2485_, 4, v___x_2484_);
return v___x_2485_;
}
}
}
}
}
else
{
lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2556_; 
lean_inc(v_r_2412_);
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_inc(v_size_2408_);
lean_dec(v_r_2407_);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_r_2402_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; lean_object* v_unused_2561_; 
v_unused_2557_ = lean_ctor_get(v_r_2402_, 4);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_r_2402_, 3);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_r_2402_, 2);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_r_2402_, 1);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_r_2402_, 0);
lean_dec(v_unused_2561_);
v___x_2494_ = v_r_2402_;
v_isShared_2495_ = v_isSharedCheck_2556_;
goto v_resetjp_2493_;
}
else
{
lean_dec(v_r_2402_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2556_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_size_2496_; lean_object* v_k_2497_; lean_object* v_v_2498_; lean_object* v_l_2499_; lean_object* v_r_2500_; lean_object* v_size_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v_size_2496_ = lean_ctor_get(v_l_2411_, 0);
v_k_2497_ = lean_ctor_get(v_l_2411_, 1);
v_v_2498_ = lean_ctor_get(v_l_2411_, 2);
v_l_2499_ = lean_ctor_get(v_l_2411_, 3);
v_r_2500_ = lean_ctor_get(v_l_2411_, 4);
v_size_2501_ = lean_ctor_get(v_r_2412_, 0);
v___x_2502_ = lean_unsigned_to_nat(2u);
v___x_2503_ = lean_nat_mul(v___x_2502_, v_size_2501_);
v___x_2504_ = lean_nat_dec_lt(v_size_2496_, v___x_2503_);
lean_dec(v___x_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2531_; 
lean_inc(v_r_2500_);
lean_inc(v_l_2499_);
lean_inc(v_v_2498_);
lean_inc(v_k_2497_);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_l_2411_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; 
v_unused_2532_ = lean_ctor_get(v_l_2411_, 4);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v_l_2411_, 3);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_l_2411_, 2);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_l_2411_, 1);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_l_2411_, 0);
lean_dec(v_unused_2536_);
v___x_2506_ = v_l_2411_;
v_isShared_2507_ = v_isSharedCheck_2531_;
goto v_resetjp_2505_;
}
else
{
lean_dec(v_l_2411_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2531_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2523_; 
v___x_2508_ = lean_unsigned_to_nat(1u);
v___x_2509_ = lean_nat_add(v___x_2508_, v_size_2403_);
v___x_2510_ = lean_nat_add(v___x_2509_, v_size_2408_);
lean_dec(v_size_2408_);
if (lean_obj_tag(v_l_2499_) == 0)
{
lean_object* v_size_2529_; 
v_size_2529_ = lean_ctor_get(v_l_2499_, 0);
lean_inc(v_size_2529_);
v___y_2523_ = v_size_2529_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_unsigned_to_nat(0u);
v___y_2523_ = v___x_2530_;
goto v___jp_2522_;
}
v___jp_2511_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2515_ = lean_nat_add(v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 4, v_r_2412_);
lean_ctor_set(v___x_2506_, 3, v_r_2500_);
lean_ctor_set(v___x_2506_, 2, v_v_2410_);
lean_ctor_set(v___x_2506_, 1, v_k_2409_);
lean_ctor_set(v___x_2506_, 0, v___x_2515_);
v___x_2517_ = v___x_2506_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_r_2500_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_r_2412_);
v___x_2517_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2519_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 4, v___x_2517_);
lean_ctor_set(v___x_2494_, 3, v___y_2512_);
lean_ctor_set(v___x_2494_, 2, v_v_2498_);
lean_ctor_set(v___x_2494_, 1, v_k_2497_);
lean_ctor_set(v___x_2494_, 0, v___x_2510_);
v___x_2519_ = v___x_2494_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_k_2497_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_v_2498_);
lean_ctor_set(v_reuseFailAlloc_2520_, 3, v___y_2512_);
lean_ctor_set(v_reuseFailAlloc_2520_, 4, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
v___jp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = lean_nat_add(v___x_2509_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec(v___x_2509_);
v___x_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set(v___x_2525_, 1, v_k_2399_);
lean_ctor_set(v___x_2525_, 2, v_v_2400_);
lean_ctor_set(v___x_2525_, 3, v_l_2401_);
lean_ctor_set(v___x_2525_, 4, v_l_2499_);
v___x_2526_ = lean_nat_add(v___x_2508_, v_size_2501_);
if (lean_obj_tag(v_r_2500_) == 0)
{
lean_object* v_size_2527_; 
v_size_2527_ = lean_ctor_get(v_r_2500_, 0);
lean_inc(v_size_2527_);
v___y_2512_ = v___x_2525_;
v___y_2513_ = v___x_2526_;
v___y_2514_ = v_size_2527_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_unsigned_to_nat(0u);
v___y_2512_ = v___x_2525_;
v___y_2513_ = v___x_2526_;
v___y_2514_ = v___x_2528_;
goto v___jp_2511_;
}
}
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2537_ = lean_unsigned_to_nat(1u);
v___x_2538_ = lean_nat_add(v___x_2537_, v_size_2403_);
v___x_2539_ = lean_nat_add(v___x_2538_, v_size_2408_);
lean_dec(v_size_2408_);
v___x_2540_ = lean_nat_add(v___x_2538_, v_size_2496_);
lean_dec(v___x_2538_);
lean_inc_ref(v_l_2401_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 4, v_l_2411_);
lean_ctor_set(v___x_2494_, 3, v_l_2401_);
lean_ctor_set(v___x_2494_, 2, v_v_2400_);
lean_ctor_set(v___x_2494_, 1, v_k_2399_);
lean_ctor_set(v___x_2494_, 0, v___x_2540_);
v___x_2542_ = v___x_2494_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_l_2401_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_l_2411_);
v___x_2542_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_isSharedCheck_2549_ = !lean_is_exclusive(v_l_2401_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; lean_object* v_unused_2551_; lean_object* v_unused_2552_; lean_object* v_unused_2553_; lean_object* v_unused_2554_; 
v_unused_2550_ = lean_ctor_get(v_l_2401_, 4);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_l_2401_, 3);
lean_dec(v_unused_2551_);
v_unused_2552_ = lean_ctor_get(v_l_2401_, 2);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v_l_2401_, 1);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_l_2401_, 0);
lean_dec(v_unused_2554_);
v___x_2544_ = v_l_2401_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_dec(v_l_2401_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 4, v_r_2412_);
lean_ctor_set(v___x_2544_, 3, v___x_2542_);
lean_ctor_set(v___x_2544_, 2, v_v_2410_);
lean_ctor_set(v___x_2544_, 1, v_k_2409_);
lean_ctor_set(v___x_2544_, 0, v___x_2539_);
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_r_2412_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2562_; 
v_l_2562_ = lean_ctor_get(v_l_2401_, 3);
if (lean_obj_tag(v_l_2562_) == 0)
{
lean_object* v_r_2563_; 
lean_inc_ref(v_l_2562_);
v_r_2563_ = lean_ctor_get(v_l_2401_, 4);
lean_inc(v_r_2563_);
if (lean_obj_tag(v_r_2563_) == 0)
{
lean_object* v_size_2564_; lean_object* v_k_2565_; lean_object* v_v_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2589_; 
v_size_2564_ = lean_ctor_get(v_l_2401_, 0);
v_k_2565_ = lean_ctor_get(v_l_2401_, 1);
v_v_2566_ = lean_ctor_get(v_l_2401_, 2);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_l_2401_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; lean_object* v_unused_2591_; 
v_unused_2590_ = lean_ctor_get(v_l_2401_, 4);
lean_dec(v_unused_2590_);
v_unused_2591_ = lean_ctor_get(v_l_2401_, 3);
lean_dec(v_unused_2591_);
v___x_2568_ = v_l_2401_;
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_v_2566_);
lean_inc(v_k_2565_);
lean_inc(v_size_2564_);
lean_dec(v_l_2401_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_size_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v_size_2570_ = lean_ctor_get(v_r_2563_, 0);
v___x_2571_ = lean_unsigned_to_nat(1u);
v___x_2572_ = lean_nat_add(v___x_2571_, v_size_2564_);
lean_dec(v_size_2564_);
v___x_2573_ = lean_nat_add(v___x_2571_, v_size_2570_);
lean_inc_ref(v_r_2563_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 4, v_r_2402_);
lean_ctor_set(v___x_2568_, 3, v_r_2563_);
lean_ctor_set(v___x_2568_, 2, v_v_2400_);
lean_ctor_set(v___x_2568_, 1, v_k_2399_);
lean_ctor_set(v___x_2568_, 0, v___x_2573_);
v___x_2575_ = v___x_2568_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2588_, 3, v_r_2563_);
lean_ctor_set(v_reuseFailAlloc_2588_, 4, v_r_2402_);
v___x_2575_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_isSharedCheck_2582_ = !lean_is_exclusive(v_r_2563_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; 
v_unused_2583_ = lean_ctor_get(v_r_2563_, 4);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_r_2563_, 3);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_r_2563_, 2);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_r_2563_, 1);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_r_2563_, 0);
lean_dec(v_unused_2587_);
v___x_2577_ = v_r_2563_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_dec(v_r_2563_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 4, v___x_2575_);
lean_ctor_set(v___x_2577_, 3, v_l_2562_);
lean_ctor_set(v___x_2577_, 2, v_v_2566_);
lean_ctor_set(v___x_2577_, 1, v_k_2565_);
lean_ctor_set(v___x_2577_, 0, v___x_2572_);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_2565_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_2566_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_l_2562_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___x_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
else
{
lean_object* v_k_2592_; lean_object* v_v_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2603_; 
v_k_2592_ = lean_ctor_get(v_l_2401_, 1);
v_v_2593_ = lean_ctor_get(v_l_2401_, 2);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_l_2401_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; lean_object* v_unused_2605_; lean_object* v_unused_2606_; 
v_unused_2604_ = lean_ctor_get(v_l_2401_, 4);
lean_dec(v_unused_2604_);
v_unused_2605_ = lean_ctor_get(v_l_2401_, 3);
lean_dec(v_unused_2605_);
v_unused_2606_ = lean_ctor_get(v_l_2401_, 0);
lean_dec(v_unused_2606_);
v___x_2595_ = v_l_2401_;
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_v_2593_);
lean_inc(v_k_2592_);
lean_dec(v_l_2401_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = lean_unsigned_to_nat(3u);
v___x_2598_ = lean_unsigned_to_nat(1u);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 3, v_r_2563_);
lean_ctor_set(v___x_2595_, 2, v_v_2400_);
lean_ctor_set(v___x_2595_, 1, v_k_2399_);
lean_ctor_set(v___x_2595_, 0, v___x_2598_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_r_2563_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_r_2563_);
v___x_2600_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2597_);
lean_ctor_set(v___x_2601_, 1, v_k_2592_);
lean_ctor_set(v___x_2601_, 2, v_v_2593_);
lean_ctor_set(v___x_2601_, 3, v_l_2562_);
lean_ctor_set(v___x_2601_, 4, v___x_2600_);
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_r_2607_; 
v_r_2607_ = lean_ctor_get(v_l_2401_, 4);
lean_inc(v_r_2607_);
if (lean_obj_tag(v_r_2607_) == 0)
{
lean_object* v_k_2608_; lean_object* v_v_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2631_; 
lean_inc(v_l_2562_);
v_k_2608_ = lean_ctor_get(v_l_2401_, 1);
v_v_2609_ = lean_ctor_get(v_l_2401_, 2);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_l_2401_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; 
v_unused_2632_ = lean_ctor_get(v_l_2401_, 4);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_l_2401_, 3);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_l_2401_, 0);
lean_dec(v_unused_2634_);
v___x_2611_ = v_l_2401_;
v_isShared_2612_ = v_isSharedCheck_2631_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_v_2609_);
lean_inc(v_k_2608_);
lean_dec(v_l_2401_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2631_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v_k_2613_; lean_object* v_v_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2627_; 
v_k_2613_ = lean_ctor_get(v_r_2607_, 1);
v_v_2614_ = lean_ctor_get(v_r_2607_, 2);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_r_2607_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; lean_object* v_unused_2629_; lean_object* v_unused_2630_; 
v_unused_2628_ = lean_ctor_get(v_r_2607_, 4);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_r_2607_, 3);
lean_dec(v_unused_2629_);
v_unused_2630_ = lean_ctor_get(v_r_2607_, 0);
lean_dec(v_unused_2630_);
v___x_2616_ = v_r_2607_;
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_v_2614_);
lean_inc(v_k_2613_);
lean_dec(v_r_2607_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = lean_unsigned_to_nat(3u);
v___x_2619_ = lean_unsigned_to_nat(1u);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 4, v_l_2562_);
lean_ctor_set(v___x_2616_, 3, v_l_2562_);
lean_ctor_set(v___x_2616_, 2, v_v_2609_);
lean_ctor_set(v___x_2616_, 1, v_k_2608_);
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_k_2608_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_v_2609_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_l_2562_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_l_2562_);
v___x_2621_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 4, v_l_2562_);
lean_ctor_set(v___x_2611_, 2, v_v_2400_);
lean_ctor_set(v___x_2611_, 1, v_k_2399_);
lean_ctor_set(v___x_2611_, 0, v___x_2619_);
v___x_2623_ = v___x_2611_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_l_2562_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_l_2562_);
v___x_2623_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2618_);
lean_ctor_set(v___x_2624_, 1, v_k_2613_);
lean_ctor_set(v___x_2624_, 2, v_v_2614_);
lean_ctor_set(v___x_2624_, 3, v___x_2621_);
lean_ctor_set(v___x_2624_, 4, v___x_2623_);
return v___x_2624_;
}
}
}
}
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_unsigned_to_nat(2u);
v___x_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v_k_2399_);
lean_ctor_set(v___x_2636_, 2, v_v_2400_);
lean_ctor_set(v___x_2636_, 3, v_l_2401_);
lean_ctor_set(v___x_2636_, 4, v_r_2607_);
return v___x_2636_;
}
}
}
}
else
{
if (lean_obj_tag(v_r_2402_) == 0)
{
lean_object* v_l_2637_; 
v_l_2637_ = lean_ctor_get(v_r_2402_, 3);
lean_inc(v_l_2637_);
if (lean_obj_tag(v_l_2637_) == 0)
{
lean_object* v_r_2638_; 
v_r_2638_ = lean_ctor_get(v_r_2402_, 4);
lean_inc(v_r_2638_);
if (lean_obj_tag(v_r_2638_) == 0)
{
lean_object* v_size_2639_; lean_object* v_k_2640_; lean_object* v_v_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2653_; 
v_size_2639_ = lean_ctor_get(v_r_2402_, 0);
v_k_2640_ = lean_ctor_get(v_r_2402_, 1);
v_v_2641_ = lean_ctor_get(v_r_2402_, 2);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_r_2402_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; lean_object* v_unused_2655_; 
v_unused_2654_ = lean_ctor_get(v_r_2402_, 4);
lean_dec(v_unused_2654_);
v_unused_2655_ = lean_ctor_get(v_r_2402_, 3);
lean_dec(v_unused_2655_);
v___x_2643_ = v_r_2402_;
v_isShared_2644_ = v_isSharedCheck_2653_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_v_2641_);
lean_inc(v_k_2640_);
lean_inc(v_size_2639_);
lean_dec(v_r_2402_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2653_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_size_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v_size_2645_ = lean_ctor_get(v_l_2637_, 0);
v___x_2646_ = lean_unsigned_to_nat(1u);
v___x_2647_ = lean_nat_add(v___x_2646_, v_size_2639_);
lean_dec(v_size_2639_);
v___x_2648_ = lean_nat_add(v___x_2646_, v_size_2645_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 4, v_l_2637_);
lean_ctor_set(v___x_2643_, 3, v_l_2401_);
lean_ctor_set(v___x_2643_, 2, v_v_2400_);
lean_ctor_set(v___x_2643_, 1, v_k_2399_);
lean_ctor_set(v___x_2643_, 0, v___x_2648_);
v___x_2650_ = v___x_2643_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_l_2401_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_l_2637_);
v___x_2650_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2647_);
lean_ctor_set(v___x_2651_, 1, v_k_2640_);
lean_ctor_set(v___x_2651_, 2, v_v_2641_);
lean_ctor_set(v___x_2651_, 3, v___x_2650_);
lean_ctor_set(v___x_2651_, 4, v_r_2638_);
return v___x_2651_;
}
}
}
else
{
lean_object* v_k_2656_; lean_object* v_v_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2679_; 
v_k_2656_ = lean_ctor_get(v_r_2402_, 1);
v_v_2657_ = lean_ctor_get(v_r_2402_, 2);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_r_2402_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; 
v_unused_2680_ = lean_ctor_get(v_r_2402_, 4);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_r_2402_, 3);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_r_2402_, 0);
lean_dec(v_unused_2682_);
v___x_2659_ = v_r_2402_;
v_isShared_2660_ = v_isSharedCheck_2679_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_v_2657_);
lean_inc(v_k_2656_);
lean_dec(v_r_2402_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2679_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_k_2661_; lean_object* v_v_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2675_; 
v_k_2661_ = lean_ctor_get(v_l_2637_, 1);
v_v_2662_ = lean_ctor_get(v_l_2637_, 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_l_2637_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; lean_object* v_unused_2677_; lean_object* v_unused_2678_; 
v_unused_2676_ = lean_ctor_get(v_l_2637_, 4);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_l_2637_, 3);
lean_dec(v_unused_2677_);
v_unused_2678_ = lean_ctor_get(v_l_2637_, 0);
lean_dec(v_unused_2678_);
v___x_2664_ = v_l_2637_;
v_isShared_2665_ = v_isSharedCheck_2675_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_v_2662_);
lean_inc(v_k_2661_);
lean_dec(v_l_2637_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2675_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2666_ = lean_unsigned_to_nat(3u);
v___x_2667_ = lean_unsigned_to_nat(1u);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 4, v_r_2638_);
lean_ctor_set(v___x_2664_, 3, v_r_2638_);
lean_ctor_set(v___x_2664_, 2, v_v_2400_);
lean_ctor_set(v___x_2664_, 1, v_k_2399_);
lean_ctor_set(v___x_2664_, 0, v___x_2667_);
v___x_2669_ = v___x_2664_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2674_, 3, v_r_2638_);
lean_ctor_set(v_reuseFailAlloc_2674_, 4, v_r_2638_);
v___x_2669_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 3, v_r_2638_);
lean_ctor_set(v___x_2659_, 0, v___x_2667_);
v___x_2671_ = v___x_2659_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_k_2656_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_v_2657_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v_r_2638_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v_r_2638_);
v___x_2671_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2666_);
lean_ctor_set(v___x_2672_, 1, v_k_2661_);
lean_ctor_set(v___x_2672_, 2, v_v_2662_);
lean_ctor_set(v___x_2672_, 3, v___x_2669_);
lean_ctor_set(v___x_2672_, 4, v___x_2671_);
return v___x_2672_;
}
}
}
}
}
}
else
{
lean_object* v_r_2683_; 
v_r_2683_ = lean_ctor_get(v_r_2402_, 4);
lean_inc(v_r_2683_);
if (lean_obj_tag(v_r_2683_) == 0)
{
lean_object* v_k_2684_; lean_object* v_v_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2695_; 
v_k_2684_ = lean_ctor_get(v_r_2402_, 1);
v_v_2685_ = lean_ctor_get(v_r_2402_, 2);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_r_2402_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; lean_object* v_unused_2697_; lean_object* v_unused_2698_; 
v_unused_2696_ = lean_ctor_get(v_r_2402_, 4);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_r_2402_, 3);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v_r_2402_, 0);
lean_dec(v_unused_2698_);
v___x_2687_ = v_r_2402_;
v_isShared_2688_ = v_isSharedCheck_2695_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_v_2685_);
lean_inc(v_k_2684_);
lean_dec(v_r_2402_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2695_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2689_ = lean_unsigned_to_nat(3u);
v___x_2690_ = lean_unsigned_to_nat(1u);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 4, v_l_2637_);
lean_ctor_set(v___x_2687_, 2, v_v_2400_);
lean_ctor_set(v___x_2687_, 1, v_k_2399_);
lean_ctor_set(v___x_2687_, 0, v___x_2690_);
v___x_2692_ = v___x_2687_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_k_2399_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_v_2400_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_l_2637_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v_l_2637_);
v___x_2692_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2689_);
lean_ctor_set(v___x_2693_, 1, v_k_2684_);
lean_ctor_set(v___x_2693_, 2, v_v_2685_);
lean_ctor_set(v___x_2693_, 3, v___x_2692_);
lean_ctor_set(v___x_2693_, 4, v_r_2683_);
return v___x_2693_;
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_unsigned_to_nat(2u);
v___x_2700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v_k_2399_);
lean_ctor_set(v___x_2700_, 2, v_v_2400_);
lean_ctor_set(v___x_2700_, 3, v_r_2683_);
lean_ctor_set(v___x_2700_, 4, v_r_2402_);
return v___x_2700_;
}
}
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v_k_2399_);
lean_ctor_set(v___x_2702_, 2, v_v_2400_);
lean_ctor_set(v___x_2702_, 3, v_r_2402_);
lean_ctor_set(v___x_2702_, 4, v_r_2402_);
return v___x_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance(lean_object* v_00_u03b1_2703_, lean_object* v_00_u03b2_2704_, lean_object* v_k_2705_, lean_object* v_v_2706_, lean_object* v_l_2707_, lean_object* v_r_2708_, lean_object* v_hl_2709_, lean_object* v_hr_2710_, lean_object* v_h_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2705_, v_v_2706_, v_l_2707_, v_r_2708_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(lean_object* v_msg_2713_){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = lean_box(1);
v___x_2715_ = lean_panic_fn_borrowed(v___x_2714_, v_msg_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0(lean_object* v_00_u03b1_2716_, lean_object* v_00_u03b2_2717_, lean_object* v_msg_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v_msg_2718_);
return v___x_2719_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2722_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2723_ = lean_unsigned_to_nat(36u);
v___x_2724_ = lean_unsigned_to_nat(393u);
v___x_2725_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2726_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2727_ = l_mkPanicMessageWithDecl(v___x_2726_, v___x_2725_, v___x_2724_, v___x_2723_, v___x_2722_);
return v___x_2727_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2728_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2729_ = lean_unsigned_to_nat(22u);
v___x_2730_ = lean_unsigned_to_nat(394u);
v___x_2731_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2732_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2733_ = l_mkPanicMessageWithDecl(v___x_2732_, v___x_2731_, v___x_2730_, v___x_2729_, v___x_2728_);
return v___x_2733_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2734_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2735_ = lean_unsigned_to_nat(36u);
v___x_2736_ = lean_unsigned_to_nat(383u);
v___x_2737_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2738_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2739_ = l_mkPanicMessageWithDecl(v___x_2738_, v___x_2737_, v___x_2736_, v___x_2735_, v___x_2734_);
return v___x_2739_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2740_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__1));
v___x_2741_ = lean_unsigned_to_nat(22u);
v___x_2742_ = lean_unsigned_to_nat(384u);
v___x_2743_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__0));
v___x_2744_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2745_ = l_mkPanicMessageWithDecl(v___x_2744_, v___x_2743_, v___x_2742_, v___x_2741_, v___x_2740_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(lean_object* v_k_2746_, lean_object* v_v_2747_, lean_object* v_l_2748_, lean_object* v_r_2749_){
_start:
{
if (lean_obj_tag(v_l_2748_) == 0)
{
if (lean_obj_tag(v_r_2749_) == 0)
{
lean_object* v_size_2750_; lean_object* v_k_2751_; lean_object* v_v_2752_; lean_object* v_l_2753_; lean_object* v_r_2754_; lean_object* v_size_2755_; lean_object* v_k_2756_; lean_object* v_v_2757_; lean_object* v_l_2758_; lean_object* v_r_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v_size_2750_ = lean_ctor_get(v_l_2748_, 0);
v_k_2751_ = lean_ctor_get(v_l_2748_, 1);
v_v_2752_ = lean_ctor_get(v_l_2748_, 2);
v_l_2753_ = lean_ctor_get(v_l_2748_, 3);
v_r_2754_ = lean_ctor_get(v_l_2748_, 4);
lean_inc(v_r_2754_);
v_size_2755_ = lean_ctor_get(v_r_2749_, 0);
v_k_2756_ = lean_ctor_get(v_r_2749_, 1);
v_v_2757_ = lean_ctor_get(v_r_2749_, 2);
v_l_2758_ = lean_ctor_get(v_r_2749_, 3);
lean_inc(v_l_2758_);
v_r_2759_ = lean_ctor_get(v_r_2749_, 4);
v___x_2760_ = lean_unsigned_to_nat(3u);
v___x_2761_ = lean_nat_mul(v___x_2760_, v_size_2750_);
v___x_2762_ = lean_nat_dec_lt(v___x_2761_, v_size_2755_);
lean_dec(v___x_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
lean_dec(v_l_2758_);
v___x_2763_ = lean_nat_mul(v___x_2760_, v_size_2755_);
v___x_2764_ = lean_nat_dec_lt(v___x_2763_, v_size_2750_);
lean_dec(v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec(v_r_2754_);
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2766_ = lean_nat_add(v___x_2765_, v_size_2750_);
v___x_2767_ = lean_nat_add(v___x_2766_, v_size_2755_);
lean_dec(v___x_2766_);
v___x_2768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v_k_2746_);
lean_ctor_set(v___x_2768_, 2, v_v_2747_);
lean_ctor_set(v___x_2768_, 3, v_l_2748_);
lean_ctor_set(v___x_2768_, 4, v_r_2749_);
return v___x_2768_;
}
else
{
lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2838_; 
lean_inc(v_l_2753_);
lean_inc(v_v_2752_);
lean_inc(v_k_2751_);
lean_inc(v_size_2750_);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_l_2748_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; lean_object* v_unused_2840_; lean_object* v_unused_2841_; lean_object* v_unused_2842_; lean_object* v_unused_2843_; 
v_unused_2839_ = lean_ctor_get(v_l_2748_, 4);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v_l_2748_, 3);
lean_dec(v_unused_2840_);
v_unused_2841_ = lean_ctor_get(v_l_2748_, 2);
lean_dec(v_unused_2841_);
v_unused_2842_ = lean_ctor_get(v_l_2748_, 1);
lean_dec(v_unused_2842_);
v_unused_2843_ = lean_ctor_get(v_l_2748_, 0);
lean_dec(v_unused_2843_);
v___x_2770_ = v_l_2748_;
v_isShared_2771_ = v_isSharedCheck_2838_;
goto v_resetjp_2769_;
}
else
{
lean_dec(v_l_2748_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2838_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
if (lean_obj_tag(v_l_2753_) == 0)
{
if (lean_obj_tag(v_r_2754_) == 0)
{
lean_object* v_size_2772_; lean_object* v_size_2773_; lean_object* v_k_2774_; lean_object* v_v_2775_; lean_object* v_l_2776_; lean_object* v_r_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v_size_2772_ = lean_ctor_get(v_l_2753_, 0);
v_size_2773_ = lean_ctor_get(v_r_2754_, 0);
v_k_2774_ = lean_ctor_get(v_r_2754_, 1);
v_v_2775_ = lean_ctor_get(v_r_2754_, 2);
v_l_2776_ = lean_ctor_get(v_r_2754_, 3);
v_r_2777_ = lean_ctor_get(v_r_2754_, 4);
v___x_2778_ = lean_unsigned_to_nat(2u);
v___x_2779_ = lean_nat_mul(v___x_2778_, v_size_2772_);
v___x_2780_ = lean_nat_dec_lt(v_size_2773_, v___x_2779_);
lean_dec(v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2819_; 
lean_inc(v_r_2777_);
lean_inc(v_l_2776_);
lean_inc(v_v_2775_);
lean_inc(v_k_2774_);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_r_2754_);
if (v_isSharedCheck_2819_ == 0)
{
lean_object* v_unused_2820_; lean_object* v_unused_2821_; lean_object* v_unused_2822_; lean_object* v_unused_2823_; lean_object* v_unused_2824_; 
v_unused_2820_ = lean_ctor_get(v_r_2754_, 4);
lean_dec(v_unused_2820_);
v_unused_2821_ = lean_ctor_get(v_r_2754_, 3);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_r_2754_, 2);
lean_dec(v_unused_2822_);
v_unused_2823_ = lean_ctor_get(v_r_2754_, 1);
lean_dec(v_unused_2823_);
v_unused_2824_ = lean_ctor_get(v_r_2754_, 0);
lean_dec(v_unused_2824_);
v___x_2782_ = v_r_2754_;
v_isShared_2783_ = v_isSharedCheck_2819_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v_r_2754_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2819_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___x_2807_; lean_object* v___y_2809_; 
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = lean_nat_add(v___x_2784_, v_size_2750_);
lean_dec(v_size_2750_);
v___x_2786_ = lean_nat_add(v___x_2785_, v_size_2755_);
lean_dec(v___x_2785_);
v___x_2807_ = lean_nat_add(v___x_2784_, v_size_2772_);
if (lean_obj_tag(v_l_2776_) == 0)
{
lean_object* v_size_2817_; 
v_size_2817_ = lean_ctor_get(v_l_2776_, 0);
lean_inc(v_size_2817_);
v___y_2809_ = v_size_2817_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_unsigned_to_nat(0u);
v___y_2809_ = v___x_2818_;
goto v___jp_2808_;
}
v___jp_2787_:
{
lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2791_ = lean_nat_add(v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_inc_ref(v_r_2749_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 4, v_r_2749_);
lean_ctor_set(v___x_2782_, 3, v_r_2777_);
lean_ctor_set(v___x_2782_, 2, v_v_2747_);
lean_ctor_set(v___x_2782_, 1, v_k_2746_);
lean_ctor_set(v___x_2782_, 0, v___x_2791_);
v___x_2793_ = v___x_2782_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_r_2777_);
lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_r_2749_);
v___x_2793_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_isSharedCheck_2800_ = !lean_is_exclusive(v_r_2749_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; lean_object* v_unused_2802_; lean_object* v_unused_2803_; lean_object* v_unused_2804_; lean_object* v_unused_2805_; 
v_unused_2801_ = lean_ctor_get(v_r_2749_, 4);
lean_dec(v_unused_2801_);
v_unused_2802_ = lean_ctor_get(v_r_2749_, 3);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_r_2749_, 2);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_r_2749_, 1);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_r_2749_, 0);
lean_dec(v_unused_2805_);
v___x_2795_ = v_r_2749_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_dec(v_r_2749_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 4, v___x_2793_);
lean_ctor_set(v___x_2795_, 3, v___y_2788_);
lean_ctor_set(v___x_2795_, 2, v_v_2775_);
lean_ctor_set(v___x_2795_, 1, v_k_2774_);
lean_ctor_set(v___x_2795_, 0, v___x_2786_);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_k_2774_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_v_2775_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v___y_2788_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v___x_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
v___jp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = lean_nat_add(v___x_2807_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec(v___x_2807_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 4, v_l_2776_);
lean_ctor_set(v___x_2770_, 0, v___x_2810_);
v___x_2812_ = v___x_2770_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_k_2751_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_v_2752_);
lean_ctor_set(v_reuseFailAlloc_2816_, 3, v_l_2753_);
lean_ctor_set(v_reuseFailAlloc_2816_, 4, v_l_2776_);
v___x_2812_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_nat_add(v___x_2784_, v_size_2755_);
if (lean_obj_tag(v_r_2777_) == 0)
{
lean_object* v_size_2814_; 
v_size_2814_ = lean_ctor_get(v_r_2777_, 0);
lean_inc(v_size_2814_);
v___y_2788_ = v___x_2812_;
v___y_2789_ = v___x_2813_;
v___y_2790_ = v_size_2814_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_unsigned_to_nat(0u);
v___y_2788_ = v___x_2812_;
v___y_2789_ = v___x_2813_;
v___y_2790_ = v___x_2815_;
goto v___jp_2787_;
}
}
}
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_nat_add(v___x_2825_, v_size_2750_);
lean_dec(v_size_2750_);
v___x_2827_ = lean_nat_add(v___x_2826_, v_size_2755_);
lean_dec(v___x_2826_);
v___x_2828_ = lean_nat_add(v___x_2825_, v_size_2755_);
v___x_2829_ = lean_nat_add(v___x_2828_, v_size_2773_);
lean_dec(v___x_2828_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 4, v_r_2749_);
lean_ctor_set(v___x_2770_, 3, v_r_2754_);
lean_ctor_set(v___x_2770_, 2, v_v_2747_);
lean_ctor_set(v___x_2770_, 1, v_k_2746_);
lean_ctor_set(v___x_2770_, 0, v___x_2829_);
v___x_2831_ = v___x_2770_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_r_2754_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_r_2749_);
v___x_2831_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2827_);
lean_ctor_set(v___x_2832_, 1, v_k_2751_);
lean_ctor_set(v___x_2832_, 2, v_v_2752_);
lean_ctor_set(v___x_2832_, 3, v_l_2753_);
lean_ctor_set(v___x_2832_, 4, v___x_2831_);
return v___x_2832_;
}
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec_ref(v_l_2753_);
lean_del_object(v___x_2770_);
lean_dec(v_v_2752_);
lean_dec(v_k_2751_);
lean_dec(v_size_2750_);
lean_dec_ref(v_r_2749_);
lean_dec(v_v_2747_);
lean_dec(v_k_2746_);
v___x_2834_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__2);
v___x_2835_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2834_);
return v___x_2835_;
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_del_object(v___x_2770_);
lean_dec(v_r_2754_);
lean_dec(v_v_2752_);
lean_dec(v_k_2751_);
lean_dec_ref(v_r_2749_);
lean_dec(v_size_2750_);
lean_dec(v_v_2747_);
lean_dec(v_k_2746_);
v___x_2836_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__3);
v___x_2837_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2836_);
return v___x_2837_;
}
}
}
}
else
{
lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2911_; 
lean_inc(v_r_2759_);
lean_inc(v_v_2757_);
lean_inc(v_k_2756_);
lean_inc(v_size_2755_);
lean_dec(v_r_2754_);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_r_2749_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; lean_object* v_unused_2913_; lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; 
v_unused_2912_ = lean_ctor_get(v_r_2749_, 4);
lean_dec(v_unused_2912_);
v_unused_2913_ = lean_ctor_get(v_r_2749_, 3);
lean_dec(v_unused_2913_);
v_unused_2914_ = lean_ctor_get(v_r_2749_, 2);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_r_2749_, 1);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_r_2749_, 0);
lean_dec(v_unused_2916_);
v___x_2845_ = v_r_2749_;
v_isShared_2846_ = v_isSharedCheck_2911_;
goto v_resetjp_2844_;
}
else
{
lean_dec(v_r_2749_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2911_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
if (lean_obj_tag(v_l_2758_) == 0)
{
if (lean_obj_tag(v_r_2759_) == 0)
{
lean_object* v_size_2847_; lean_object* v_k_2848_; lean_object* v_v_2849_; lean_object* v_l_2850_; lean_object* v_r_2851_; lean_object* v_size_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v_size_2847_ = lean_ctor_get(v_l_2758_, 0);
v_k_2848_ = lean_ctor_get(v_l_2758_, 1);
v_v_2849_ = lean_ctor_get(v_l_2758_, 2);
v_l_2850_ = lean_ctor_get(v_l_2758_, 3);
v_r_2851_ = lean_ctor_get(v_l_2758_, 4);
v_size_2852_ = lean_ctor_get(v_r_2759_, 0);
v___x_2853_ = lean_unsigned_to_nat(2u);
v___x_2854_ = lean_nat_mul(v___x_2853_, v_size_2852_);
v___x_2855_ = lean_nat_dec_lt(v_size_2847_, v___x_2854_);
lean_dec(v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2882_; 
lean_inc(v_r_2851_);
lean_inc(v_l_2850_);
lean_inc(v_v_2849_);
lean_inc(v_k_2848_);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_l_2758_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; lean_object* v_unused_2884_; lean_object* v_unused_2885_; lean_object* v_unused_2886_; lean_object* v_unused_2887_; 
v_unused_2883_ = lean_ctor_get(v_l_2758_, 4);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_l_2758_, 3);
lean_dec(v_unused_2884_);
v_unused_2885_ = lean_ctor_get(v_l_2758_, 2);
lean_dec(v_unused_2885_);
v_unused_2886_ = lean_ctor_get(v_l_2758_, 1);
lean_dec(v_unused_2886_);
v_unused_2887_ = lean_ctor_get(v_l_2758_, 0);
lean_dec(v_unused_2887_);
v___x_2857_ = v_l_2758_;
v_isShared_2858_ = v_isSharedCheck_2882_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v_l_2758_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2882_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2874_; 
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_add(v___x_2859_, v_size_2750_);
v___x_2861_ = lean_nat_add(v___x_2860_, v_size_2755_);
lean_dec(v_size_2755_);
if (lean_obj_tag(v_l_2850_) == 0)
{
lean_object* v_size_2880_; 
v_size_2880_ = lean_ctor_get(v_l_2850_, 0);
lean_inc(v_size_2880_);
v___y_2874_ = v_size_2880_;
goto v___jp_2873_;
}
else
{
lean_object* v___x_2881_; 
v___x_2881_ = lean_unsigned_to_nat(0u);
v___y_2874_ = v___x_2881_;
goto v___jp_2873_;
}
v___jp_2862_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2866_ = lean_nat_add(v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 4, v_r_2759_);
lean_ctor_set(v___x_2857_, 3, v_r_2851_);
lean_ctor_set(v___x_2857_, 2, v_v_2757_);
lean_ctor_set(v___x_2857_, 1, v_k_2756_);
lean_ctor_set(v___x_2857_, 0, v___x_2866_);
v___x_2868_ = v___x_2857_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_k_2756_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_v_2757_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_r_2851_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_r_2759_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 4, v___x_2868_);
lean_ctor_set(v___x_2845_, 3, v___y_2863_);
lean_ctor_set(v___x_2845_, 2, v_v_2849_);
lean_ctor_set(v___x_2845_, 1, v_k_2848_);
lean_ctor_set(v___x_2845_, 0, v___x_2861_);
v___x_2870_ = v___x_2845_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_k_2848_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_v_2849_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v___y_2863_);
lean_ctor_set(v_reuseFailAlloc_2871_, 4, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
v___jp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_nat_add(v___x_2860_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec(v___x_2860_);
v___x_2876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v_k_2746_);
lean_ctor_set(v___x_2876_, 2, v_v_2747_);
lean_ctor_set(v___x_2876_, 3, v_l_2748_);
lean_ctor_set(v___x_2876_, 4, v_l_2850_);
v___x_2877_ = lean_nat_add(v___x_2859_, v_size_2852_);
if (lean_obj_tag(v_r_2851_) == 0)
{
lean_object* v_size_2878_; 
v_size_2878_ = lean_ctor_get(v_r_2851_, 0);
lean_inc(v_size_2878_);
v___y_2863_ = v___x_2876_;
v___y_2864_ = v___x_2877_;
v___y_2865_ = v_size_2878_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_unsigned_to_nat(0u);
v___y_2863_ = v___x_2876_;
v___y_2864_ = v___x_2877_;
v___y_2865_ = v___x_2879_;
goto v___jp_2862_;
}
}
}
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2888_ = lean_unsigned_to_nat(1u);
v___x_2889_ = lean_nat_add(v___x_2888_, v_size_2750_);
v___x_2890_ = lean_nat_add(v___x_2889_, v_size_2755_);
lean_dec(v_size_2755_);
v___x_2891_ = lean_nat_add(v___x_2889_, v_size_2847_);
lean_dec(v___x_2889_);
lean_inc_ref(v_l_2748_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 4, v_l_2758_);
lean_ctor_set(v___x_2845_, 3, v_l_2748_);
lean_ctor_set(v___x_2845_, 2, v_v_2747_);
lean_ctor_set(v___x_2845_, 1, v_k_2746_);
lean_ctor_set(v___x_2845_, 0, v___x_2891_);
v___x_2893_ = v___x_2845_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2906_, 3, v_l_2748_);
lean_ctor_set(v_reuseFailAlloc_2906_, 4, v_l_2758_);
v___x_2893_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_isSharedCheck_2900_ = !lean_is_exclusive(v_l_2748_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; lean_object* v_unused_2902_; lean_object* v_unused_2903_; lean_object* v_unused_2904_; lean_object* v_unused_2905_; 
v_unused_2901_ = lean_ctor_get(v_l_2748_, 4);
lean_dec(v_unused_2901_);
v_unused_2902_ = lean_ctor_get(v_l_2748_, 3);
lean_dec(v_unused_2902_);
v_unused_2903_ = lean_ctor_get(v_l_2748_, 2);
lean_dec(v_unused_2903_);
v_unused_2904_ = lean_ctor_get(v_l_2748_, 1);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v_l_2748_, 0);
lean_dec(v_unused_2905_);
v___x_2895_ = v_l_2748_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_dec(v_l_2748_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 4, v_r_2759_);
lean_ctor_set(v___x_2895_, 3, v___x_2893_);
lean_ctor_set(v___x_2895_, 2, v_v_2757_);
lean_ctor_set(v___x_2895_, 1, v_k_2756_);
lean_ctor_set(v___x_2895_, 0, v___x_2890_);
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_k_2756_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_v_2757_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_r_2759_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref(v_l_2758_);
lean_del_object(v___x_2845_);
lean_dec(v_v_2757_);
lean_dec(v_k_2756_);
lean_dec(v_size_2755_);
lean_dec_ref(v_l_2748_);
lean_dec(v_v_2747_);
lean_dec(v_k_2746_);
v___x_2907_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__4);
v___x_2908_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2907_);
return v___x_2908_;
}
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_del_object(v___x_2845_);
lean_dec(v_r_2759_);
lean_dec(v_v_2757_);
lean_dec(v_k_2756_);
lean_dec(v_size_2755_);
lean_dec_ref(v_l_2748_);
lean_dec(v_v_2747_);
lean_dec(v_k_2746_);
v___x_2909_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_balance_x21___redArg___closed__5);
v___x_2910_ = l_panic___at___00Std_DTreeMap_Internal_Impl_balance_x21_spec__0___redArg(v___x_2909_);
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_l_2917_; 
v_l_2917_ = lean_ctor_get(v_l_2748_, 3);
if (lean_obj_tag(v_l_2917_) == 0)
{
lean_object* v_r_2918_; 
lean_inc_ref(v_l_2917_);
v_r_2918_ = lean_ctor_get(v_l_2748_, 4);
lean_inc(v_r_2918_);
if (lean_obj_tag(v_r_2918_) == 0)
{
lean_object* v_size_2919_; lean_object* v_k_2920_; lean_object* v_v_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2944_; 
v_size_2919_ = lean_ctor_get(v_l_2748_, 0);
v_k_2920_ = lean_ctor_get(v_l_2748_, 1);
v_v_2921_ = lean_ctor_get(v_l_2748_, 2);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_l_2748_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; lean_object* v_unused_2946_; 
v_unused_2945_ = lean_ctor_get(v_l_2748_, 4);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_l_2748_, 3);
lean_dec(v_unused_2946_);
v___x_2923_ = v_l_2748_;
v_isShared_2924_ = v_isSharedCheck_2944_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_v_2921_);
lean_inc(v_k_2920_);
lean_inc(v_size_2919_);
lean_dec(v_l_2748_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2944_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_size_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v_size_2925_ = lean_ctor_get(v_r_2918_, 0);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_add(v___x_2926_, v_size_2919_);
lean_dec(v_size_2919_);
v___x_2928_ = lean_nat_add(v___x_2926_, v_size_2925_);
lean_inc_ref(v_r_2918_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 4, v_r_2749_);
lean_ctor_set(v___x_2923_, 3, v_r_2918_);
lean_ctor_set(v___x_2923_, 2, v_v_2747_);
lean_ctor_set(v___x_2923_, 1, v_k_2746_);
lean_ctor_set(v___x_2923_, 0, v___x_2928_);
v___x_2930_ = v___x_2923_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_r_2918_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_r_2749_);
v___x_2930_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_isSharedCheck_2937_ = !lean_is_exclusive(v_r_2918_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; lean_object* v_unused_2939_; lean_object* v_unused_2940_; lean_object* v_unused_2941_; lean_object* v_unused_2942_; 
v_unused_2938_ = lean_ctor_get(v_r_2918_, 4);
lean_dec(v_unused_2938_);
v_unused_2939_ = lean_ctor_get(v_r_2918_, 3);
lean_dec(v_unused_2939_);
v_unused_2940_ = lean_ctor_get(v_r_2918_, 2);
lean_dec(v_unused_2940_);
v_unused_2941_ = lean_ctor_get(v_r_2918_, 1);
lean_dec(v_unused_2941_);
v_unused_2942_ = lean_ctor_get(v_r_2918_, 0);
lean_dec(v_unused_2942_);
v___x_2932_ = v_r_2918_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_dec(v_r_2918_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 4, v___x_2930_);
lean_ctor_set(v___x_2932_, 3, v_l_2917_);
lean_ctor_set(v___x_2932_, 2, v_v_2921_);
lean_ctor_set(v___x_2932_, 1, v_k_2920_);
lean_ctor_set(v___x_2932_, 0, v___x_2927_);
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_k_2920_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_v_2921_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_l_2917_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v___x_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
else
{
lean_object* v_k_2947_; lean_object* v_v_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2958_; 
v_k_2947_ = lean_ctor_get(v_l_2748_, 1);
v_v_2948_ = lean_ctor_get(v_l_2748_, 2);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_l_2748_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; lean_object* v_unused_2960_; lean_object* v_unused_2961_; 
v_unused_2959_ = lean_ctor_get(v_l_2748_, 4);
lean_dec(v_unused_2959_);
v_unused_2960_ = lean_ctor_get(v_l_2748_, 3);
lean_dec(v_unused_2960_);
v_unused_2961_ = lean_ctor_get(v_l_2748_, 0);
lean_dec(v_unused_2961_);
v___x_2950_ = v_l_2748_;
v_isShared_2951_ = v_isSharedCheck_2958_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_v_2948_);
lean_inc(v_k_2947_);
lean_dec(v_l_2748_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2958_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2952_ = lean_unsigned_to_nat(3u);
v___x_2953_ = lean_unsigned_to_nat(1u);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 3, v_r_2918_);
lean_ctor_set(v___x_2950_, 2, v_v_2747_);
lean_ctor_set(v___x_2950_, 1, v_k_2746_);
lean_ctor_set(v___x_2950_, 0, v___x_2953_);
v___x_2955_ = v___x_2950_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_r_2918_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_r_2918_);
v___x_2955_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2952_);
lean_ctor_set(v___x_2956_, 1, v_k_2947_);
lean_ctor_set(v___x_2956_, 2, v_v_2948_);
lean_ctor_set(v___x_2956_, 3, v_l_2917_);
lean_ctor_set(v___x_2956_, 4, v___x_2955_);
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_r_2962_; 
v_r_2962_ = lean_ctor_get(v_l_2748_, 4);
lean_inc(v_r_2962_);
if (lean_obj_tag(v_r_2962_) == 0)
{
lean_object* v_k_2963_; lean_object* v_v_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2986_; 
lean_inc(v_l_2917_);
v_k_2963_ = lean_ctor_get(v_l_2748_, 1);
v_v_2964_ = lean_ctor_get(v_l_2748_, 2);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_l_2748_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; lean_object* v_unused_2988_; lean_object* v_unused_2989_; 
v_unused_2987_ = lean_ctor_get(v_l_2748_, 4);
lean_dec(v_unused_2987_);
v_unused_2988_ = lean_ctor_get(v_l_2748_, 3);
lean_dec(v_unused_2988_);
v_unused_2989_ = lean_ctor_get(v_l_2748_, 0);
lean_dec(v_unused_2989_);
v___x_2966_ = v_l_2748_;
v_isShared_2967_ = v_isSharedCheck_2986_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_v_2964_);
lean_inc(v_k_2963_);
lean_dec(v_l_2748_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2986_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_k_2968_; lean_object* v_v_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2982_; 
v_k_2968_ = lean_ctor_get(v_r_2962_, 1);
v_v_2969_ = lean_ctor_get(v_r_2962_, 2);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_r_2962_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; lean_object* v_unused_2984_; lean_object* v_unused_2985_; 
v_unused_2983_ = lean_ctor_get(v_r_2962_, 4);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_r_2962_, 3);
lean_dec(v_unused_2984_);
v_unused_2985_ = lean_ctor_get(v_r_2962_, 0);
lean_dec(v_unused_2985_);
v___x_2971_ = v_r_2962_;
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_v_2969_);
lean_inc(v_k_2968_);
lean_dec(v_r_2962_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2973_ = lean_unsigned_to_nat(3u);
v___x_2974_ = lean_unsigned_to_nat(1u);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 4, v_l_2917_);
lean_ctor_set(v___x_2971_, 3, v_l_2917_);
lean_ctor_set(v___x_2971_, 2, v_v_2964_);
lean_ctor_set(v___x_2971_, 1, v_k_2963_);
lean_ctor_set(v___x_2971_, 0, v___x_2974_);
v___x_2976_ = v___x_2971_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_k_2963_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_v_2964_);
lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_l_2917_);
lean_ctor_set(v_reuseFailAlloc_2981_, 4, v_l_2917_);
v___x_2976_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2978_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 4, v_l_2917_);
lean_ctor_set(v___x_2966_, 2, v_v_2747_);
lean_ctor_set(v___x_2966_, 1, v_k_2746_);
lean_ctor_set(v___x_2966_, 0, v___x_2974_);
v___x_2978_ = v___x_2966_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_l_2917_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_l_2917_);
v___x_2978_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2973_);
lean_ctor_set(v___x_2979_, 1, v_k_2968_);
lean_ctor_set(v___x_2979_, 2, v_v_2969_);
lean_ctor_set(v___x_2979_, 3, v___x_2976_);
lean_ctor_set(v___x_2979_, 4, v___x_2978_);
return v___x_2979_;
}
}
}
}
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_unsigned_to_nat(2u);
v___x_2991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v_k_2746_);
lean_ctor_set(v___x_2991_, 2, v_v_2747_);
lean_ctor_set(v___x_2991_, 3, v_l_2748_);
lean_ctor_set(v___x_2991_, 4, v_r_2962_);
return v___x_2991_;
}
}
}
}
else
{
if (lean_obj_tag(v_r_2749_) == 0)
{
lean_object* v_l_2992_; 
v_l_2992_ = lean_ctor_get(v_r_2749_, 3);
lean_inc(v_l_2992_);
if (lean_obj_tag(v_l_2992_) == 0)
{
lean_object* v_r_2993_; 
v_r_2993_ = lean_ctor_get(v_r_2749_, 4);
lean_inc(v_r_2993_);
if (lean_obj_tag(v_r_2993_) == 0)
{
lean_object* v_size_2994_; lean_object* v_k_2995_; lean_object* v_v_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3008_; 
v_size_2994_ = lean_ctor_get(v_r_2749_, 0);
v_k_2995_ = lean_ctor_get(v_r_2749_, 1);
v_v_2996_ = lean_ctor_get(v_r_2749_, 2);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_r_2749_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; lean_object* v_unused_3010_; 
v_unused_3009_ = lean_ctor_get(v_r_2749_, 4);
lean_dec(v_unused_3009_);
v_unused_3010_ = lean_ctor_get(v_r_2749_, 3);
lean_dec(v_unused_3010_);
v___x_2998_ = v_r_2749_;
v_isShared_2999_ = v_isSharedCheck_3008_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_v_2996_);
lean_inc(v_k_2995_);
lean_inc(v_size_2994_);
lean_dec(v_r_2749_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3008_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v_size_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v_size_3000_ = lean_ctor_get(v_l_2992_, 0);
v___x_3001_ = lean_unsigned_to_nat(1u);
v___x_3002_ = lean_nat_add(v___x_3001_, v_size_2994_);
lean_dec(v_size_2994_);
v___x_3003_ = lean_nat_add(v___x_3001_, v_size_3000_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 4, v_l_2992_);
lean_ctor_set(v___x_2998_, 3, v_l_2748_);
lean_ctor_set(v___x_2998_, 2, v_v_2747_);
lean_ctor_set(v___x_2998_, 1, v_k_2746_);
lean_ctor_set(v___x_2998_, 0, v___x_3003_);
v___x_3005_ = v___x_2998_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v_l_2748_);
lean_ctor_set(v_reuseFailAlloc_3007_, 4, v_l_2992_);
v___x_3005_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3002_);
lean_ctor_set(v___x_3006_, 1, v_k_2995_);
lean_ctor_set(v___x_3006_, 2, v_v_2996_);
lean_ctor_set(v___x_3006_, 3, v___x_3005_);
lean_ctor_set(v___x_3006_, 4, v_r_2993_);
return v___x_3006_;
}
}
}
else
{
lean_object* v_k_3011_; lean_object* v_v_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3034_; 
v_k_3011_ = lean_ctor_get(v_r_2749_, 1);
v_v_3012_ = lean_ctor_get(v_r_2749_, 2);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_r_2749_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; lean_object* v_unused_3036_; lean_object* v_unused_3037_; 
v_unused_3035_ = lean_ctor_get(v_r_2749_, 4);
lean_dec(v_unused_3035_);
v_unused_3036_ = lean_ctor_get(v_r_2749_, 3);
lean_dec(v_unused_3036_);
v_unused_3037_ = lean_ctor_get(v_r_2749_, 0);
lean_dec(v_unused_3037_);
v___x_3014_ = v_r_2749_;
v_isShared_3015_ = v_isSharedCheck_3034_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_v_3012_);
lean_inc(v_k_3011_);
lean_dec(v_r_2749_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3034_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v_k_3016_; lean_object* v_v_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3030_; 
v_k_3016_ = lean_ctor_get(v_l_2992_, 1);
v_v_3017_ = lean_ctor_get(v_l_2992_, 2);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_l_2992_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; lean_object* v_unused_3032_; lean_object* v_unused_3033_; 
v_unused_3031_ = lean_ctor_get(v_l_2992_, 4);
lean_dec(v_unused_3031_);
v_unused_3032_ = lean_ctor_get(v_l_2992_, 3);
lean_dec(v_unused_3032_);
v_unused_3033_ = lean_ctor_get(v_l_2992_, 0);
lean_dec(v_unused_3033_);
v___x_3019_ = v_l_2992_;
v_isShared_3020_ = v_isSharedCheck_3030_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_v_3017_);
lean_inc(v_k_3016_);
lean_dec(v_l_2992_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3030_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3021_ = lean_unsigned_to_nat(3u);
v___x_3022_ = lean_unsigned_to_nat(1u);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 4, v_r_2993_);
lean_ctor_set(v___x_3019_, 3, v_r_2993_);
lean_ctor_set(v___x_3019_, 2, v_v_2747_);
lean_ctor_set(v___x_3019_, 1, v_k_2746_);
lean_ctor_set(v___x_3019_, 0, v___x_3022_);
v___x_3024_ = v___x_3019_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_3029_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_3029_, 3, v_r_2993_);
lean_ctor_set(v_reuseFailAlloc_3029_, 4, v_r_2993_);
v___x_3024_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 3, v_r_2993_);
lean_ctor_set(v___x_3014_, 0, v___x_3022_);
v___x_3026_ = v___x_3014_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_k_3011_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_v_3012_);
lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_r_2993_);
lean_ctor_set(v_reuseFailAlloc_3028_, 4, v_r_2993_);
v___x_3026_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3021_);
lean_ctor_set(v___x_3027_, 1, v_k_3016_);
lean_ctor_set(v___x_3027_, 2, v_v_3017_);
lean_ctor_set(v___x_3027_, 3, v___x_3024_);
lean_ctor_set(v___x_3027_, 4, v___x_3026_);
return v___x_3027_;
}
}
}
}
}
}
else
{
lean_object* v_r_3038_; 
v_r_3038_ = lean_ctor_get(v_r_2749_, 4);
lean_inc(v_r_3038_);
if (lean_obj_tag(v_r_3038_) == 0)
{
lean_object* v_k_3039_; lean_object* v_v_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3050_; 
v_k_3039_ = lean_ctor_get(v_r_2749_, 1);
v_v_3040_ = lean_ctor_get(v_r_2749_, 2);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_r_2749_);
if (v_isSharedCheck_3050_ == 0)
{
lean_object* v_unused_3051_; lean_object* v_unused_3052_; lean_object* v_unused_3053_; 
v_unused_3051_ = lean_ctor_get(v_r_2749_, 4);
lean_dec(v_unused_3051_);
v_unused_3052_ = lean_ctor_get(v_r_2749_, 3);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v_r_2749_, 0);
lean_dec(v_unused_3053_);
v___x_3042_ = v_r_2749_;
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_v_3040_);
lean_inc(v_k_3039_);
lean_dec(v_r_2749_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3044_ = lean_unsigned_to_nat(3u);
v___x_3045_ = lean_unsigned_to_nat(1u);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 4, v_l_2992_);
lean_ctor_set(v___x_3042_, 2, v_v_2747_);
lean_ctor_set(v___x_3042_, 1, v_k_2746_);
lean_ctor_set(v___x_3042_, 0, v___x_3045_);
v___x_3047_ = v___x_3042_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_l_2992_);
lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_l_2992_);
v___x_3047_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3044_);
lean_ctor_set(v___x_3048_, 1, v_k_3039_);
lean_ctor_set(v___x_3048_, 2, v_v_3040_);
lean_ctor_set(v___x_3048_, 3, v___x_3047_);
lean_ctor_set(v___x_3048_, 4, v_r_3038_);
return v___x_3048_;
}
}
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_unsigned_to_nat(2u);
v___x_3055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v_k_2746_);
lean_ctor_set(v___x_3055_, 2, v_v_2747_);
lean_ctor_set(v___x_3055_, 3, v_r_3038_);
lean_ctor_set(v___x_3055_, 4, v_r_2749_);
return v___x_3055_;
}
}
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v_k_2746_);
lean_ctor_set(v___x_3057_, 2, v_v_2747_);
lean_ctor_set(v___x_3057_, 3, v_r_2749_);
lean_ctor_set(v___x_3057_, 4, v_r_2749_);
return v___x_3057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_x21(lean_object* v_00_u03b1_3058_, lean_object* v_00_u03b2_3059_, lean_object* v_k_3060_, lean_object* v_v_3061_, lean_object* v_l_3062_, lean_object* v_r_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_balance_x21___redArg(v_k_3060_, v_v_3061_, v_l_3062_, v_r_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin___redArg(lean_object* v_k_3065_, lean_object* v_v_3066_, lean_object* v_l_3067_, lean_object* v_r_3068_){
_start:
{
lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3075_; 
if (lean_obj_tag(v_l_3067_) == 0)
{
lean_object* v_size_3080_; 
v_size_3080_ = lean_ctor_get(v_l_3067_, 0);
lean_inc(v_size_3080_);
v___y_3075_ = v_size_3080_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___y_3075_ = v___x_3081_;
goto v___jp_3074_;
}
v___jp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_nat_add(v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
v___x_3073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v_k_3065_);
lean_ctor_set(v___x_3073_, 2, v_v_3066_);
lean_ctor_set(v___x_3073_, 3, v_l_3067_);
lean_ctor_set(v___x_3073_, 4, v_r_3068_);
return v___x_3073_;
}
v___jp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = lean_unsigned_to_nat(1u);
v___x_3077_ = lean_nat_add(v___y_3075_, v___x_3076_);
lean_dec(v___y_3075_);
if (lean_obj_tag(v_r_3068_) == 0)
{
lean_object* v_size_3078_; 
v_size_3078_ = lean_ctor_get(v_r_3068_, 0);
lean_inc(v_size_3078_);
v___y_3070_ = v___x_3077_;
v___y_3071_ = v_size_3078_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_unsigned_to_nat(0u);
v___y_3070_ = v___x_3077_;
v___y_3071_ = v___x_3079_;
goto v___jp_3069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_bin(lean_object* v_00_u03b1_3082_, lean_object* v_00_u03b2_3083_, lean_object* v_k_3084_, lean_object* v_v_3085_, lean_object* v_l_3086_, lean_object* v_r_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3084_, v_v_3085_, v_l_3086_, v_r_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL___redArg(lean_object* v_k_3089_, lean_object* v_v_3090_, lean_object* v_l_3091_, lean_object* v_rk_3092_, lean_object* v_rv_3093_, lean_object* v_rl_3094_, lean_object* v_rr_3095_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3089_, v_v_3090_, v_l_3091_, v_rl_3094_);
v___x_3097_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_rk_3092_, v_rv_3093_, v___x_3096_, v_rr_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleL(lean_object* v_00_u03b1_3098_, lean_object* v_00_u03b2_3099_, lean_object* v_k_3100_, lean_object* v_v_3101_, lean_object* v_l_3102_, lean_object* v_rk_3103_, lean_object* v_rv_3104_, lean_object* v_rl_3105_, lean_object* v_rr_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Std_DTreeMap_Internal_Impl_singleL___redArg(v_k_3100_, v_v_3101_, v_l_3102_, v_rk_3103_, v_rv_3104_, v_rl_3105_, v_rr_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR___redArg(lean_object* v_k_3108_, lean_object* v_v_3109_, lean_object* v_lk_3110_, lean_object* v_lv_3111_, lean_object* v_ll_3112_, lean_object* v_lr_3113_, lean_object* v_r_3114_){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3108_, v_v_3109_, v_lr_3113_, v_r_3114_);
v___x_3116_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_lk_3110_, v_lv_3111_, v_ll_3112_, v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_singleR(lean_object* v_00_u03b1_3117_, lean_object* v_00_u03b2_3118_, lean_object* v_k_3119_, lean_object* v_v_3120_, lean_object* v_lk_3121_, lean_object* v_lv_3122_, lean_object* v_ll_3123_, lean_object* v_lr_3124_, lean_object* v_r_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Std_DTreeMap_Internal_Impl_singleR___redArg(v_k_3119_, v_v_3120_, v_lk_3121_, v_lv_3122_, v_ll_3123_, v_lr_3124_, v_r_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL___redArg(lean_object* v_k_3127_, lean_object* v_v_3128_, lean_object* v_l_3129_, lean_object* v_rk_3130_, lean_object* v_rv_3131_, lean_object* v_rlk_3132_, lean_object* v_rlv_3133_, lean_object* v_rll_3134_, lean_object* v_rlr_3135_, lean_object* v_rr_3136_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3127_, v_v_3128_, v_l_3129_, v_rll_3134_);
v___x_3138_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_rk_3130_, v_rv_3131_, v_rlr_3135_, v_rr_3136_);
v___x_3139_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_rlk_3132_, v_rlv_3133_, v___x_3137_, v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleL(lean_object* v_00_u03b1_3140_, lean_object* v_00_u03b2_3141_, lean_object* v_k_3142_, lean_object* v_v_3143_, lean_object* v_l_3144_, lean_object* v_rk_3145_, lean_object* v_rv_3146_, lean_object* v_rlk_3147_, lean_object* v_rlv_3148_, lean_object* v_rll_3149_, lean_object* v_rlr_3150_, lean_object* v_rr_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Std_DTreeMap_Internal_Impl_doubleL___redArg(v_k_3142_, v_v_3143_, v_l_3144_, v_rk_3145_, v_rv_3146_, v_rlk_3147_, v_rlv_3148_, v_rll_3149_, v_rlr_3150_, v_rr_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR___redArg(lean_object* v_k_3153_, lean_object* v_v_3154_, lean_object* v_lk_3155_, lean_object* v_lv_3156_, lean_object* v_ll_3157_, lean_object* v_lrk_3158_, lean_object* v_lrv_3159_, lean_object* v_lrl_3160_, lean_object* v_lrr_3161_, lean_object* v_r_3162_){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_lk_3155_, v_lv_3156_, v_ll_3157_, v_lrl_3160_);
v___x_3164_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3153_, v_v_3154_, v_lrr_3161_, v_r_3162_);
v___x_3165_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_lrk_3158_, v_lrv_3159_, v___x_3163_, v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_doubleR(lean_object* v_00_u03b1_3166_, lean_object* v_00_u03b2_3167_, lean_object* v_k_3168_, lean_object* v_v_3169_, lean_object* v_lk_3170_, lean_object* v_lv_3171_, lean_object* v_ll_3172_, lean_object* v_lrk_3173_, lean_object* v_lrv_3174_, lean_object* v_lrl_3175_, lean_object* v_lrr_3176_, lean_object* v_r_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Std_DTreeMap_Internal_Impl_doubleR___redArg(v_k_3168_, v_v_3169_, v_lk_3170_, v_lv_3171_, v_ll_3172_, v_lrk_3173_, v_lrv_3174_, v_lrl_3175_, v_lrr_3176_, v_r_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL___redArg(lean_object* v_k_3179_, lean_object* v_v_3180_, lean_object* v_l_3181_, lean_object* v_rk_3182_, lean_object* v_rv_3183_, lean_object* v_rl_3184_, lean_object* v_rr_3185_){
_start:
{
lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3200_; 
if (lean_obj_tag(v_rl_3184_) == 0)
{
lean_object* v_size_3204_; 
v_size_3204_ = lean_ctor_get(v_rl_3184_, 0);
lean_inc(v_size_3204_);
v___y_3200_ = v_size_3204_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_unsigned_to_nat(0u);
v___y_3200_ = v___x_3205_;
goto v___jp_3199_;
}
v___jp_3186_:
{
lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = lean_nat_mul(v___y_3187_, v___y_3189_);
lean_dec(v___y_3189_);
v___x_3191_ = lean_nat_dec_lt(v___y_3188_, v___x_3190_);
lean_dec(v___x_3190_);
lean_dec(v___y_3188_);
if (v___x_3191_ == 0)
{
if (lean_obj_tag(v_rl_3184_) == 0)
{
lean_object* v_k_3192_; lean_object* v_v_3193_; lean_object* v_l_3194_; lean_object* v_r_3195_; lean_object* v___x_3196_; 
v_k_3192_ = lean_ctor_get(v_rl_3184_, 1);
lean_inc(v_k_3192_);
v_v_3193_ = lean_ctor_get(v_rl_3184_, 2);
lean_inc(v_v_3193_);
v_l_3194_ = lean_ctor_get(v_rl_3184_, 3);
lean_inc(v_l_3194_);
v_r_3195_ = lean_ctor_get(v_rl_3184_, 4);
lean_inc(v_r_3195_);
lean_dec_ref(v_rl_3184_);
v___x_3196_ = l_Std_DTreeMap_Internal_Impl_doubleL___redArg(v_k_3179_, v_v_3180_, v_l_3181_, v_rk_3182_, v_rv_3183_, v_k_3192_, v_v_3193_, v_l_3194_, v_r_3195_, v_rr_3185_);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Std_DTreeMap_Internal_Impl_singleL___redArg(v_k_3179_, v_v_3180_, v_l_3181_, v_rk_3182_, v_rv_3183_, v_rl_3184_, v_rr_3185_);
return v___x_3197_;
}
}
else
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Std_DTreeMap_Internal_Impl_singleL___redArg(v_k_3179_, v_v_3180_, v_l_3181_, v_rk_3182_, v_rv_3183_, v_rl_3184_, v_rr_3185_);
return v___x_3198_;
}
}
v___jp_3199_:
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_unsigned_to_nat(2u);
if (lean_obj_tag(v_rr_3185_) == 0)
{
lean_object* v_size_3202_; 
v_size_3202_ = lean_ctor_get(v_rr_3185_, 0);
lean_inc(v_size_3202_);
v___y_3187_ = v___x_3201_;
v___y_3188_ = v___y_3200_;
v___y_3189_ = v_size_3202_;
goto v___jp_3186_;
}
else
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_unsigned_to_nat(0u);
v___y_3187_ = v___x_3201_;
v___y_3188_ = v___y_3200_;
v___y_3189_ = v___x_3203_;
goto v___jp_3186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateL(lean_object* v_00_u03b1_3206_, lean_object* v_00_u03b2_3207_, lean_object* v_k_3208_, lean_object* v_v_3209_, lean_object* v_l_3210_, lean_object* v_rk_3211_, lean_object* v_rv_3212_, lean_object* v_rl_3213_, lean_object* v_rr_3214_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Std_DTreeMap_Internal_Impl_rotateL___redArg(v_k_3208_, v_v_3209_, v_l_3210_, v_rk_3211_, v_rv_3212_, v_rl_3213_, v_rr_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter___redArg(lean_object* v_l_3216_, lean_object* v_h__1_3217_, lean_object* v_h__2_3218_){
_start:
{
if (lean_obj_tag(v_l_3216_) == 0)
{
lean_object* v_size_3219_; lean_object* v_k_3220_; lean_object* v_v_3221_; lean_object* v_l_3222_; lean_object* v_r_3223_; lean_object* v___x_3224_; 
lean_dec(v_h__1_3217_);
v_size_3219_ = lean_ctor_get(v_l_3216_, 0);
lean_inc(v_size_3219_);
v_k_3220_ = lean_ctor_get(v_l_3216_, 1);
lean_inc(v_k_3220_);
v_v_3221_ = lean_ctor_get(v_l_3216_, 2);
lean_inc(v_v_3221_);
v_l_3222_ = lean_ctor_get(v_l_3216_, 3);
lean_inc(v_l_3222_);
v_r_3223_ = lean_ctor_get(v_l_3216_, 4);
lean_inc(v_r_3223_);
lean_dec_ref(v_l_3216_);
v___x_3224_ = lean_apply_5(v_h__2_3218_, v_size_3219_, v_k_3220_, v_v_3221_, v_l_3222_, v_r_3223_);
return v___x_3224_;
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec(v_h__2_3218_);
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_apply_1(v_h__1_3217_, v___x_3225_);
return v___x_3226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__5_splitter(lean_object* v_00_u03b1_3227_, lean_object* v_00_u03b2_3228_, lean_object* v_motive_3229_, lean_object* v_l_3230_, lean_object* v_h__1_3231_, lean_object* v_h__2_3232_){
_start:
{
if (lean_obj_tag(v_l_3230_) == 0)
{
lean_object* v_size_3233_; lean_object* v_k_3234_; lean_object* v_v_3235_; lean_object* v_l_3236_; lean_object* v_r_3237_; lean_object* v___x_3238_; 
lean_dec(v_h__1_3231_);
v_size_3233_ = lean_ctor_get(v_l_3230_, 0);
lean_inc(v_size_3233_);
v_k_3234_ = lean_ctor_get(v_l_3230_, 1);
lean_inc(v_k_3234_);
v_v_3235_ = lean_ctor_get(v_l_3230_, 2);
lean_inc(v_v_3235_);
v_l_3236_ = lean_ctor_get(v_l_3230_, 3);
lean_inc(v_l_3236_);
v_r_3237_ = lean_ctor_get(v_l_3230_, 4);
lean_inc(v_r_3237_);
lean_dec_ref(v_l_3230_);
v___x_3238_ = lean_apply_5(v_h__2_3232_, v_size_3233_, v_k_3234_, v_v_3235_, v_l_3236_, v_r_3237_);
return v___x_3238_;
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_dec(v_h__2_3232_);
v___x_3239_ = lean_box(0);
v___x_3240_ = lean_apply_1(v_h__1_3231_, v___x_3239_);
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR___redArg(lean_object* v_k_3241_, lean_object* v_v_3242_, lean_object* v_lk_3243_, lean_object* v_lv_3244_, lean_object* v_ll_3245_, lean_object* v_lr_3246_, lean_object* v_r_3247_){
_start:
{
lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3262_; 
if (lean_obj_tag(v_lr_3246_) == 0)
{
lean_object* v_size_3266_; 
v_size_3266_ = lean_ctor_get(v_lr_3246_, 0);
lean_inc(v_size_3266_);
v___y_3262_ = v_size_3266_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_unsigned_to_nat(0u);
v___y_3262_ = v___x_3267_;
goto v___jp_3261_;
}
v___jp_3248_:
{
lean_object* v___x_3252_; uint8_t v___x_3253_; 
v___x_3252_ = lean_nat_mul(v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
v___x_3253_ = lean_nat_dec_lt(v___y_3249_, v___x_3252_);
lean_dec(v___x_3252_);
lean_dec(v___y_3249_);
if (v___x_3253_ == 0)
{
if (lean_obj_tag(v_lr_3246_) == 0)
{
lean_object* v_k_3254_; lean_object* v_v_3255_; lean_object* v_l_3256_; lean_object* v_r_3257_; lean_object* v___x_3258_; 
v_k_3254_ = lean_ctor_get(v_lr_3246_, 1);
lean_inc(v_k_3254_);
v_v_3255_ = lean_ctor_get(v_lr_3246_, 2);
lean_inc(v_v_3255_);
v_l_3256_ = lean_ctor_get(v_lr_3246_, 3);
lean_inc(v_l_3256_);
v_r_3257_ = lean_ctor_get(v_lr_3246_, 4);
lean_inc(v_r_3257_);
lean_dec_ref(v_lr_3246_);
v___x_3258_ = l_Std_DTreeMap_Internal_Impl_doubleR___redArg(v_k_3241_, v_v_3242_, v_lk_3243_, v_lv_3244_, v_ll_3245_, v_k_3254_, v_v_3255_, v_l_3256_, v_r_3257_, v_r_3247_);
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Std_DTreeMap_Internal_Impl_singleR___redArg(v_k_3241_, v_v_3242_, v_lk_3243_, v_lv_3244_, v_ll_3245_, v_lr_3246_, v_r_3247_);
return v___x_3259_;
}
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Std_DTreeMap_Internal_Impl_singleR___redArg(v_k_3241_, v_v_3242_, v_lk_3243_, v_lv_3244_, v_ll_3245_, v_lr_3246_, v_r_3247_);
return v___x_3260_;
}
}
v___jp_3261_:
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_unsigned_to_nat(2u);
if (lean_obj_tag(v_ll_3245_) == 0)
{
lean_object* v_size_3264_; 
v_size_3264_ = lean_ctor_get(v_ll_3245_, 0);
lean_inc(v_size_3264_);
v___y_3249_ = v___y_3262_;
v___y_3250_ = v___x_3263_;
v___y_3251_ = v_size_3264_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_unsigned_to_nat(0u);
v___y_3249_ = v___y_3262_;
v___y_3250_ = v___x_3263_;
v___y_3251_ = v___x_3265_;
goto v___jp_3248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_rotateR(lean_object* v_00_u03b1_3268_, lean_object* v_00_u03b2_3269_, lean_object* v_k_3270_, lean_object* v_v_3271_, lean_object* v_lk_3272_, lean_object* v_lv_3273_, lean_object* v_ll_3274_, lean_object* v_lr_3275_, lean_object* v_r_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_rotateR___redArg(v_k_3270_, v_v_3271_, v_lk_3272_, v_lv_3273_, v_ll_3274_, v_lr_3275_, v_r_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098___redArg(lean_object* v_k_3278_, lean_object* v_v_3279_, lean_object* v_l_3280_, lean_object* v_r_3281_){
_start:
{
lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3306_; 
if (lean_obj_tag(v_l_3280_) == 0)
{
lean_object* v_size_3309_; 
v_size_3309_ = lean_ctor_get(v_l_3280_, 0);
lean_inc(v_size_3309_);
v___y_3306_ = v_size_3309_;
goto v___jp_3305_;
}
else
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_unsigned_to_nat(0u);
v___y_3306_ = v___x_3310_;
goto v___jp_3305_;
}
v___jp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = lean_nat_add(v___y_3283_, v___y_3284_);
v___x_3286_ = lean_unsigned_to_nat(1u);
v___x_3287_ = lean_nat_dec_le(v___x_3285_, v___x_3286_);
lean_dec(v___x_3285_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3288_ = lean_unsigned_to_nat(3u);
v___x_3289_ = lean_nat_mul(v___x_3288_, v___y_3283_);
v___x_3290_ = lean_nat_dec_lt(v___x_3289_, v___y_3284_);
lean_dec(v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = lean_nat_mul(v___x_3288_, v___y_3284_);
lean_dec(v___y_3284_);
v___x_3292_ = lean_nat_dec_lt(v___x_3291_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec(v___x_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3278_, v_v_3279_, v_l_3280_, v_r_3281_);
return v___x_3293_;
}
else
{
lean_object* v_k_3294_; lean_object* v_v_3295_; lean_object* v_l_3296_; lean_object* v_r_3297_; lean_object* v___x_3298_; 
v_k_3294_ = lean_ctor_get(v_l_3280_, 1);
lean_inc(v_k_3294_);
v_v_3295_ = lean_ctor_get(v_l_3280_, 2);
lean_inc(v_v_3295_);
v_l_3296_ = lean_ctor_get(v_l_3280_, 3);
lean_inc(v_l_3296_);
v_r_3297_ = lean_ctor_get(v_l_3280_, 4);
lean_inc(v_r_3297_);
lean_dec(v_l_3280_);
v___x_3298_ = l_Std_DTreeMap_Internal_Impl_rotateR___redArg(v_k_3278_, v_v_3279_, v_k_3294_, v_v_3295_, v_l_3296_, v_r_3297_, v_r_3281_);
return v___x_3298_;
}
}
else
{
lean_object* v_k_3299_; lean_object* v_v_3300_; lean_object* v_l_3301_; lean_object* v_r_3302_; lean_object* v___x_3303_; 
lean_dec(v___y_3284_);
lean_dec(v___y_3283_);
v_k_3299_ = lean_ctor_get(v_r_3281_, 1);
lean_inc(v_k_3299_);
v_v_3300_ = lean_ctor_get(v_r_3281_, 2);
lean_inc(v_v_3300_);
v_l_3301_ = lean_ctor_get(v_r_3281_, 3);
lean_inc(v_l_3301_);
v_r_3302_ = lean_ctor_get(v_r_3281_, 4);
lean_inc(v_r_3302_);
lean_dec(v_r_3281_);
v___x_3303_ = l_Std_DTreeMap_Internal_Impl_rotateL___redArg(v_k_3278_, v_v_3279_, v_l_3280_, v_k_3299_, v_v_3300_, v_l_3301_, v_r_3302_);
return v___x_3303_;
}
}
else
{
lean_object* v___x_3304_; 
lean_dec(v___y_3284_);
lean_dec(v___y_3283_);
v___x_3304_ = l_Std_DTreeMap_Internal_Impl_bin___redArg(v_k_3278_, v_v_3279_, v_l_3280_, v_r_3281_);
return v___x_3304_;
}
}
v___jp_3305_:
{
if (lean_obj_tag(v_r_3281_) == 0)
{
lean_object* v_size_3307_; 
v_size_3307_ = lean_ctor_get(v_r_3281_, 0);
lean_inc(v_size_3307_);
v___y_3283_ = v___y_3306_;
v___y_3284_ = v_size_3307_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_unsigned_to_nat(0u);
v___y_3283_ = v___y_3306_;
v___y_3284_ = v___x_3308_;
goto v___jp_3282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balance_u2098(lean_object* v_00_u03b1_3311_, lean_object* v_00_u03b2_3312_, lean_object* v_k_3313_, lean_object* v_v_3314_, lean_object* v_l_3315_, lean_object* v_r_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Std_DTreeMap_Internal_Impl_balance_u2098___redArg(v_k_3313_, v_v_3314_, v_l_3315_, v_r_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter___redArg(lean_object* v_r_3318_, lean_object* v_h__1_3319_, lean_object* v_h__2_3320_, lean_object* v_h__3_3321_, lean_object* v_h__4_3322_, lean_object* v_h__5_3323_){
_start:
{
if (lean_obj_tag(v_r_3318_) == 0)
{
lean_object* v_l_3324_; 
lean_dec(v_h__1_3319_);
v_l_3324_ = lean_ctor_get(v_r_3318_, 3);
if (lean_obj_tag(v_l_3324_) == 0)
{
lean_object* v_r_3325_; 
lean_inc_ref(v_l_3324_);
lean_dec(v_h__3_3321_);
lean_dec(v_h__2_3320_);
v_r_3325_ = lean_ctor_get(v_r_3318_, 4);
if (lean_obj_tag(v_r_3325_) == 0)
{
lean_object* v_size_3326_; lean_object* v_k_3327_; lean_object* v_v_3328_; lean_object* v_size_3329_; lean_object* v_k_3330_; lean_object* v_v_3331_; lean_object* v_l_3332_; lean_object* v_r_3333_; lean_object* v_size_3334_; lean_object* v_k_3335_; lean_object* v_v_3336_; lean_object* v_l_3337_; lean_object* v_r_3338_; lean_object* v___x_3339_; 
lean_inc_ref(v_r_3325_);
lean_dec(v_h__4_3322_);
v_size_3326_ = lean_ctor_get(v_r_3318_, 0);
lean_inc(v_size_3326_);
v_k_3327_ = lean_ctor_get(v_r_3318_, 1);
lean_inc(v_k_3327_);
v_v_3328_ = lean_ctor_get(v_r_3318_, 2);
lean_inc(v_v_3328_);
lean_dec_ref(v_r_3318_);
v_size_3329_ = lean_ctor_get(v_l_3324_, 0);
lean_inc(v_size_3329_);
v_k_3330_ = lean_ctor_get(v_l_3324_, 1);
lean_inc(v_k_3330_);
v_v_3331_ = lean_ctor_get(v_l_3324_, 2);
lean_inc(v_v_3331_);
v_l_3332_ = lean_ctor_get(v_l_3324_, 3);
lean_inc(v_l_3332_);
v_r_3333_ = lean_ctor_get(v_l_3324_, 4);
lean_inc(v_r_3333_);
lean_dec_ref(v_l_3324_);
v_size_3334_ = lean_ctor_get(v_r_3325_, 0);
lean_inc(v_size_3334_);
v_k_3335_ = lean_ctor_get(v_r_3325_, 1);
lean_inc(v_k_3335_);
v_v_3336_ = lean_ctor_get(v_r_3325_, 2);
lean_inc(v_v_3336_);
v_l_3337_ = lean_ctor_get(v_r_3325_, 3);
lean_inc(v_l_3337_);
v_r_3338_ = lean_ctor_get(v_r_3325_, 4);
lean_inc(v_r_3338_);
lean_dec_ref(v_r_3325_);
v___x_3339_ = lean_apply_13(v_h__5_3323_, v_size_3326_, v_k_3327_, v_v_3328_, v_size_3329_, v_k_3330_, v_v_3331_, v_l_3332_, v_r_3333_, v_size_3334_, v_k_3335_, v_v_3336_, v_l_3337_, v_r_3338_);
return v___x_3339_;
}
else
{
lean_object* v_size_3340_; lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v_size_3343_; lean_object* v_k_3344_; lean_object* v_v_3345_; lean_object* v_l_3346_; lean_object* v_r_3347_; lean_object* v___x_3348_; 
lean_dec(v_h__5_3323_);
v_size_3340_ = lean_ctor_get(v_r_3318_, 0);
lean_inc(v_size_3340_);
v_k_3341_ = lean_ctor_get(v_r_3318_, 1);
lean_inc(v_k_3341_);
v_v_3342_ = lean_ctor_get(v_r_3318_, 2);
lean_inc(v_v_3342_);
lean_dec_ref(v_r_3318_);
v_size_3343_ = lean_ctor_get(v_l_3324_, 0);
lean_inc(v_size_3343_);
v_k_3344_ = lean_ctor_get(v_l_3324_, 1);
lean_inc(v_k_3344_);
v_v_3345_ = lean_ctor_get(v_l_3324_, 2);
lean_inc(v_v_3345_);
v_l_3346_ = lean_ctor_get(v_l_3324_, 3);
lean_inc(v_l_3346_);
v_r_3347_ = lean_ctor_get(v_l_3324_, 4);
lean_inc(v_r_3347_);
lean_dec_ref(v_l_3324_);
v___x_3348_ = lean_apply_8(v_h__4_3322_, v_size_3340_, v_k_3341_, v_v_3342_, v_size_3343_, v_k_3344_, v_v_3345_, v_l_3346_, v_r_3347_);
return v___x_3348_;
}
}
else
{
lean_object* v_r_3349_; 
lean_dec(v_h__5_3323_);
lean_dec(v_h__4_3322_);
v_r_3349_ = lean_ctor_get(v_r_3318_, 4);
if (lean_obj_tag(v_r_3349_) == 0)
{
lean_object* v_size_3350_; lean_object* v_k_3351_; lean_object* v_v_3352_; lean_object* v_size_3353_; lean_object* v_k_3354_; lean_object* v_v_3355_; lean_object* v_l_3356_; lean_object* v_r_3357_; lean_object* v___x_3358_; 
lean_inc_ref(v_r_3349_);
lean_dec(v_h__2_3320_);
v_size_3350_ = lean_ctor_get(v_r_3318_, 0);
lean_inc(v_size_3350_);
v_k_3351_ = lean_ctor_get(v_r_3318_, 1);
lean_inc(v_k_3351_);
v_v_3352_ = lean_ctor_get(v_r_3318_, 2);
lean_inc(v_v_3352_);
lean_dec_ref(v_r_3318_);
v_size_3353_ = lean_ctor_get(v_r_3349_, 0);
lean_inc(v_size_3353_);
v_k_3354_ = lean_ctor_get(v_r_3349_, 1);
lean_inc(v_k_3354_);
v_v_3355_ = lean_ctor_get(v_r_3349_, 2);
lean_inc(v_v_3355_);
v_l_3356_ = lean_ctor_get(v_r_3349_, 3);
lean_inc(v_l_3356_);
v_r_3357_ = lean_ctor_get(v_r_3349_, 4);
lean_inc(v_r_3357_);
lean_dec_ref(v_r_3349_);
v___x_3358_ = lean_apply_8(v_h__3_3321_, v_size_3350_, v_k_3351_, v_v_3352_, v_size_3353_, v_k_3354_, v_v_3355_, v_l_3356_, v_r_3357_);
return v___x_3358_;
}
else
{
lean_object* v_size_3359_; lean_object* v_k_3360_; lean_object* v_v_3361_; lean_object* v___x_3362_; 
lean_dec(v_h__3_3321_);
v_size_3359_ = lean_ctor_get(v_r_3318_, 0);
lean_inc(v_size_3359_);
v_k_3360_ = lean_ctor_get(v_r_3318_, 1);
lean_inc(v_k_3360_);
v_v_3361_ = lean_ctor_get(v_r_3318_, 2);
lean_inc(v_v_3361_);
lean_dec_ref(v_r_3318_);
v___x_3362_ = lean_apply_3(v_h__2_3320_, v_size_3359_, v_k_3360_, v_v_3361_);
return v___x_3362_;
}
}
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v_h__5_3323_);
lean_dec(v_h__4_3322_);
lean_dec(v_h__3_3321_);
lean_dec(v_h__2_3320_);
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_apply_1(v_h__1_3319_, v___x_3363_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__1_splitter(lean_object* v_00_u03b1_3365_, lean_object* v_00_u03b2_3366_, lean_object* v_motive_3367_, lean_object* v_r_3368_, lean_object* v_h__1_3369_, lean_object* v_h__2_3370_, lean_object* v_h__3_3371_, lean_object* v_h__4_3372_, lean_object* v_h__5_3373_){
_start:
{
if (lean_obj_tag(v_r_3368_) == 0)
{
lean_object* v_l_3374_; 
lean_dec(v_h__1_3369_);
v_l_3374_ = lean_ctor_get(v_r_3368_, 3);
if (lean_obj_tag(v_l_3374_) == 0)
{
lean_object* v_r_3375_; 
lean_inc_ref(v_l_3374_);
lean_dec(v_h__3_3371_);
lean_dec(v_h__2_3370_);
v_r_3375_ = lean_ctor_get(v_r_3368_, 4);
if (lean_obj_tag(v_r_3375_) == 0)
{
lean_object* v_size_3376_; lean_object* v_k_3377_; lean_object* v_v_3378_; lean_object* v_size_3379_; lean_object* v_k_3380_; lean_object* v_v_3381_; lean_object* v_l_3382_; lean_object* v_r_3383_; lean_object* v_size_3384_; lean_object* v_k_3385_; lean_object* v_v_3386_; lean_object* v_l_3387_; lean_object* v_r_3388_; lean_object* v___x_3389_; 
lean_inc_ref(v_r_3375_);
lean_dec(v_h__4_3372_);
v_size_3376_ = lean_ctor_get(v_r_3368_, 0);
lean_inc(v_size_3376_);
v_k_3377_ = lean_ctor_get(v_r_3368_, 1);
lean_inc(v_k_3377_);
v_v_3378_ = lean_ctor_get(v_r_3368_, 2);
lean_inc(v_v_3378_);
lean_dec_ref(v_r_3368_);
v_size_3379_ = lean_ctor_get(v_l_3374_, 0);
lean_inc(v_size_3379_);
v_k_3380_ = lean_ctor_get(v_l_3374_, 1);
lean_inc(v_k_3380_);
v_v_3381_ = lean_ctor_get(v_l_3374_, 2);
lean_inc(v_v_3381_);
v_l_3382_ = lean_ctor_get(v_l_3374_, 3);
lean_inc(v_l_3382_);
v_r_3383_ = lean_ctor_get(v_l_3374_, 4);
lean_inc(v_r_3383_);
lean_dec_ref(v_l_3374_);
v_size_3384_ = lean_ctor_get(v_r_3375_, 0);
lean_inc(v_size_3384_);
v_k_3385_ = lean_ctor_get(v_r_3375_, 1);
lean_inc(v_k_3385_);
v_v_3386_ = lean_ctor_get(v_r_3375_, 2);
lean_inc(v_v_3386_);
v_l_3387_ = lean_ctor_get(v_r_3375_, 3);
lean_inc(v_l_3387_);
v_r_3388_ = lean_ctor_get(v_r_3375_, 4);
lean_inc(v_r_3388_);
lean_dec_ref(v_r_3375_);
v___x_3389_ = lean_apply_13(v_h__5_3373_, v_size_3376_, v_k_3377_, v_v_3378_, v_size_3379_, v_k_3380_, v_v_3381_, v_l_3382_, v_r_3383_, v_size_3384_, v_k_3385_, v_v_3386_, v_l_3387_, v_r_3388_);
return v___x_3389_;
}
else
{
lean_object* v_size_3390_; lean_object* v_k_3391_; lean_object* v_v_3392_; lean_object* v_size_3393_; lean_object* v_k_3394_; lean_object* v_v_3395_; lean_object* v_l_3396_; lean_object* v_r_3397_; lean_object* v___x_3398_; 
lean_dec(v_h__5_3373_);
v_size_3390_ = lean_ctor_get(v_r_3368_, 0);
lean_inc(v_size_3390_);
v_k_3391_ = lean_ctor_get(v_r_3368_, 1);
lean_inc(v_k_3391_);
v_v_3392_ = lean_ctor_get(v_r_3368_, 2);
lean_inc(v_v_3392_);
lean_dec_ref(v_r_3368_);
v_size_3393_ = lean_ctor_get(v_l_3374_, 0);
lean_inc(v_size_3393_);
v_k_3394_ = lean_ctor_get(v_l_3374_, 1);
lean_inc(v_k_3394_);
v_v_3395_ = lean_ctor_get(v_l_3374_, 2);
lean_inc(v_v_3395_);
v_l_3396_ = lean_ctor_get(v_l_3374_, 3);
lean_inc(v_l_3396_);
v_r_3397_ = lean_ctor_get(v_l_3374_, 4);
lean_inc(v_r_3397_);
lean_dec_ref(v_l_3374_);
v___x_3398_ = lean_apply_8(v_h__4_3372_, v_size_3390_, v_k_3391_, v_v_3392_, v_size_3393_, v_k_3394_, v_v_3395_, v_l_3396_, v_r_3397_);
return v___x_3398_;
}
}
else
{
lean_object* v_r_3399_; 
lean_dec(v_h__5_3373_);
lean_dec(v_h__4_3372_);
v_r_3399_ = lean_ctor_get(v_r_3368_, 4);
if (lean_obj_tag(v_r_3399_) == 0)
{
lean_object* v_size_3400_; lean_object* v_k_3401_; lean_object* v_v_3402_; lean_object* v_size_3403_; lean_object* v_k_3404_; lean_object* v_v_3405_; lean_object* v_l_3406_; lean_object* v_r_3407_; lean_object* v___x_3408_; 
lean_inc_ref(v_r_3399_);
lean_dec(v_h__2_3370_);
v_size_3400_ = lean_ctor_get(v_r_3368_, 0);
lean_inc(v_size_3400_);
v_k_3401_ = lean_ctor_get(v_r_3368_, 1);
lean_inc(v_k_3401_);
v_v_3402_ = lean_ctor_get(v_r_3368_, 2);
lean_inc(v_v_3402_);
lean_dec_ref(v_r_3368_);
v_size_3403_ = lean_ctor_get(v_r_3399_, 0);
lean_inc(v_size_3403_);
v_k_3404_ = lean_ctor_get(v_r_3399_, 1);
lean_inc(v_k_3404_);
v_v_3405_ = lean_ctor_get(v_r_3399_, 2);
lean_inc(v_v_3405_);
v_l_3406_ = lean_ctor_get(v_r_3399_, 3);
lean_inc(v_l_3406_);
v_r_3407_ = lean_ctor_get(v_r_3399_, 4);
lean_inc(v_r_3407_);
lean_dec_ref(v_r_3399_);
v___x_3408_ = lean_apply_8(v_h__3_3371_, v_size_3400_, v_k_3401_, v_v_3402_, v_size_3403_, v_k_3404_, v_v_3405_, v_l_3406_, v_r_3407_);
return v___x_3408_;
}
else
{
lean_object* v_size_3409_; lean_object* v_k_3410_; lean_object* v_v_3411_; lean_object* v___x_3412_; 
lean_dec(v_h__3_3371_);
v_size_3409_ = lean_ctor_get(v_r_3368_, 0);
lean_inc(v_size_3409_);
v_k_3410_ = lean_ctor_get(v_r_3368_, 1);
lean_inc(v_k_3410_);
v_v_3411_ = lean_ctor_get(v_r_3368_, 2);
lean_inc(v_v_3411_);
lean_dec_ref(v_r_3368_);
v___x_3412_ = lean_apply_3(v_h__2_3370_, v_size_3409_, v_k_3410_, v_v_3411_);
return v___x_3412_;
}
}
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v_h__5_3373_);
lean_dec(v_h__4_3372_);
lean_dec(v_h__3_3371_);
lean_dec(v_h__2_3370_);
v___x_3413_ = lean_box(0);
v___x_3414_ = lean_apply_1(v_h__1_3369_, v___x_3413_);
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter___redArg(lean_object* v_ll_3415_, lean_object* v_lr_3416_, lean_object* v_h__1_3417_, lean_object* v_h__2_3418_, lean_object* v_h__3_3419_, lean_object* v_h__4_3420_){
_start:
{
if (lean_obj_tag(v_ll_3415_) == 0)
{
lean_dec(v_h__2_3418_);
lean_dec(v_h__1_3417_);
if (lean_obj_tag(v_lr_3416_) == 0)
{
lean_object* v_size_3421_; lean_object* v_k_3422_; lean_object* v_v_3423_; lean_object* v_l_3424_; lean_object* v_r_3425_; lean_object* v_size_3426_; lean_object* v_k_3427_; lean_object* v_v_3428_; lean_object* v_l_3429_; lean_object* v_r_3430_; lean_object* v___x_3431_; 
lean_dec(v_h__3_3419_);
v_size_3421_ = lean_ctor_get(v_ll_3415_, 0);
lean_inc(v_size_3421_);
v_k_3422_ = lean_ctor_get(v_ll_3415_, 1);
lean_inc(v_k_3422_);
v_v_3423_ = lean_ctor_get(v_ll_3415_, 2);
lean_inc(v_v_3423_);
v_l_3424_ = lean_ctor_get(v_ll_3415_, 3);
lean_inc(v_l_3424_);
v_r_3425_ = lean_ctor_get(v_ll_3415_, 4);
lean_inc(v_r_3425_);
lean_dec_ref(v_ll_3415_);
v_size_3426_ = lean_ctor_get(v_lr_3416_, 0);
lean_inc(v_size_3426_);
v_k_3427_ = lean_ctor_get(v_lr_3416_, 1);
lean_inc(v_k_3427_);
v_v_3428_ = lean_ctor_get(v_lr_3416_, 2);
lean_inc(v_v_3428_);
v_l_3429_ = lean_ctor_get(v_lr_3416_, 3);
lean_inc(v_l_3429_);
v_r_3430_ = lean_ctor_get(v_lr_3416_, 4);
lean_inc(v_r_3430_);
lean_dec_ref(v_lr_3416_);
v___x_3431_ = lean_apply_10(v_h__4_3420_, v_size_3421_, v_k_3422_, v_v_3423_, v_l_3424_, v_r_3425_, v_size_3426_, v_k_3427_, v_v_3428_, v_l_3429_, v_r_3430_);
return v___x_3431_;
}
else
{
lean_object* v_size_3432_; lean_object* v_k_3433_; lean_object* v_v_3434_; lean_object* v_l_3435_; lean_object* v_r_3436_; lean_object* v___x_3437_; 
lean_dec(v_h__4_3420_);
v_size_3432_ = lean_ctor_get(v_ll_3415_, 0);
lean_inc(v_size_3432_);
v_k_3433_ = lean_ctor_get(v_ll_3415_, 1);
lean_inc(v_k_3433_);
v_v_3434_ = lean_ctor_get(v_ll_3415_, 2);
lean_inc(v_v_3434_);
v_l_3435_ = lean_ctor_get(v_ll_3415_, 3);
lean_inc(v_l_3435_);
v_r_3436_ = lean_ctor_get(v_ll_3415_, 4);
lean_inc(v_r_3436_);
lean_dec_ref(v_ll_3415_);
v___x_3437_ = lean_apply_5(v_h__3_3419_, v_size_3432_, v_k_3433_, v_v_3434_, v_l_3435_, v_r_3436_);
return v___x_3437_;
}
}
else
{
lean_dec(v_h__4_3420_);
lean_dec(v_h__3_3419_);
if (lean_obj_tag(v_lr_3416_) == 0)
{
lean_object* v_size_3438_; lean_object* v_k_3439_; lean_object* v_v_3440_; lean_object* v_l_3441_; lean_object* v_r_3442_; lean_object* v___x_3443_; 
lean_dec(v_h__1_3417_);
v_size_3438_ = lean_ctor_get(v_lr_3416_, 0);
lean_inc(v_size_3438_);
v_k_3439_ = lean_ctor_get(v_lr_3416_, 1);
lean_inc(v_k_3439_);
v_v_3440_ = lean_ctor_get(v_lr_3416_, 2);
lean_inc(v_v_3440_);
v_l_3441_ = lean_ctor_get(v_lr_3416_, 3);
lean_inc(v_l_3441_);
v_r_3442_ = lean_ctor_get(v_lr_3416_, 4);
lean_inc(v_r_3442_);
lean_dec_ref(v_lr_3416_);
v___x_3443_ = lean_apply_5(v_h__2_3418_, v_size_3438_, v_k_3439_, v_v_3440_, v_l_3441_, v_r_3442_);
return v___x_3443_;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec(v_h__2_3418_);
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_apply_1(v_h__1_3417_, v___x_3444_);
return v___x_3445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_x21_match__3_splitter(lean_object* v_00_u03b1_3446_, lean_object* v_00_u03b2_3447_, lean_object* v_motive_3448_, lean_object* v_ll_3449_, lean_object* v_lr_3450_, lean_object* v_h__1_3451_, lean_object* v_h__2_3452_, lean_object* v_h__3_3453_, lean_object* v_h__4_3454_){
_start:
{
if (lean_obj_tag(v_ll_3449_) == 0)
{
lean_dec(v_h__2_3452_);
lean_dec(v_h__1_3451_);
if (lean_obj_tag(v_lr_3450_) == 0)
{
lean_object* v_size_3455_; lean_object* v_k_3456_; lean_object* v_v_3457_; lean_object* v_l_3458_; lean_object* v_r_3459_; lean_object* v_size_3460_; lean_object* v_k_3461_; lean_object* v_v_3462_; lean_object* v_l_3463_; lean_object* v_r_3464_; lean_object* v___x_3465_; 
lean_dec(v_h__3_3453_);
v_size_3455_ = lean_ctor_get(v_ll_3449_, 0);
lean_inc(v_size_3455_);
v_k_3456_ = lean_ctor_get(v_ll_3449_, 1);
lean_inc(v_k_3456_);
v_v_3457_ = lean_ctor_get(v_ll_3449_, 2);
lean_inc(v_v_3457_);
v_l_3458_ = lean_ctor_get(v_ll_3449_, 3);
lean_inc(v_l_3458_);
v_r_3459_ = lean_ctor_get(v_ll_3449_, 4);
lean_inc(v_r_3459_);
lean_dec_ref(v_ll_3449_);
v_size_3460_ = lean_ctor_get(v_lr_3450_, 0);
lean_inc(v_size_3460_);
v_k_3461_ = lean_ctor_get(v_lr_3450_, 1);
lean_inc(v_k_3461_);
v_v_3462_ = lean_ctor_get(v_lr_3450_, 2);
lean_inc(v_v_3462_);
v_l_3463_ = lean_ctor_get(v_lr_3450_, 3);
lean_inc(v_l_3463_);
v_r_3464_ = lean_ctor_get(v_lr_3450_, 4);
lean_inc(v_r_3464_);
lean_dec_ref(v_lr_3450_);
v___x_3465_ = lean_apply_10(v_h__4_3454_, v_size_3455_, v_k_3456_, v_v_3457_, v_l_3458_, v_r_3459_, v_size_3460_, v_k_3461_, v_v_3462_, v_l_3463_, v_r_3464_);
return v___x_3465_;
}
else
{
lean_object* v_size_3466_; lean_object* v_k_3467_; lean_object* v_v_3468_; lean_object* v_l_3469_; lean_object* v_r_3470_; lean_object* v___x_3471_; 
lean_dec(v_h__4_3454_);
v_size_3466_ = lean_ctor_get(v_ll_3449_, 0);
lean_inc(v_size_3466_);
v_k_3467_ = lean_ctor_get(v_ll_3449_, 1);
lean_inc(v_k_3467_);
v_v_3468_ = lean_ctor_get(v_ll_3449_, 2);
lean_inc(v_v_3468_);
v_l_3469_ = lean_ctor_get(v_ll_3449_, 3);
lean_inc(v_l_3469_);
v_r_3470_ = lean_ctor_get(v_ll_3449_, 4);
lean_inc(v_r_3470_);
lean_dec_ref(v_ll_3449_);
v___x_3471_ = lean_apply_5(v_h__3_3453_, v_size_3466_, v_k_3467_, v_v_3468_, v_l_3469_, v_r_3470_);
return v___x_3471_;
}
}
else
{
lean_dec(v_h__4_3454_);
lean_dec(v_h__3_3453_);
if (lean_obj_tag(v_lr_3450_) == 0)
{
lean_object* v_size_3472_; lean_object* v_k_3473_; lean_object* v_v_3474_; lean_object* v_l_3475_; lean_object* v_r_3476_; lean_object* v___x_3477_; 
lean_dec(v_h__1_3451_);
v_size_3472_ = lean_ctor_get(v_lr_3450_, 0);
lean_inc(v_size_3472_);
v_k_3473_ = lean_ctor_get(v_lr_3450_, 1);
lean_inc(v_k_3473_);
v_v_3474_ = lean_ctor_get(v_lr_3450_, 2);
lean_inc(v_v_3474_);
v_l_3475_ = lean_ctor_get(v_lr_3450_, 3);
lean_inc(v_l_3475_);
v_r_3476_ = lean_ctor_get(v_lr_3450_, 4);
lean_inc(v_r_3476_);
lean_dec_ref(v_lr_3450_);
v___x_3477_ = lean_apply_5(v_h__2_3452_, v_size_3472_, v_k_3473_, v_v_3474_, v_l_3475_, v_r_3476_);
return v___x_3477_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_dec(v_h__2_3452_);
v___x_3478_ = lean_box(0);
v___x_3479_ = lean_apply_1(v_h__1_3451_, v___x_3478_);
return v___x_3479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter___redArg(lean_object* v_ll_3480_, lean_object* v_lr_3481_, lean_object* v_h__1_3482_, lean_object* v_h__2_3483_, lean_object* v_h__3_3484_){
_start:
{
if (lean_obj_tag(v_ll_3480_) == 0)
{
lean_dec(v_h__3_3484_);
if (lean_obj_tag(v_lr_3481_) == 0)
{
lean_object* v_size_3485_; lean_object* v_k_3486_; lean_object* v_v_3487_; lean_object* v_l_3488_; lean_object* v_r_3489_; lean_object* v_size_3490_; lean_object* v_k_3491_; lean_object* v_v_3492_; lean_object* v_l_3493_; lean_object* v_r_3494_; lean_object* v___x_3495_; 
lean_dec(v_h__2_3483_);
v_size_3485_ = lean_ctor_get(v_ll_3480_, 0);
lean_inc(v_size_3485_);
v_k_3486_ = lean_ctor_get(v_ll_3480_, 1);
lean_inc(v_k_3486_);
v_v_3487_ = lean_ctor_get(v_ll_3480_, 2);
lean_inc(v_v_3487_);
v_l_3488_ = lean_ctor_get(v_ll_3480_, 3);
lean_inc(v_l_3488_);
v_r_3489_ = lean_ctor_get(v_ll_3480_, 4);
lean_inc(v_r_3489_);
lean_dec_ref(v_ll_3480_);
v_size_3490_ = lean_ctor_get(v_lr_3481_, 0);
lean_inc(v_size_3490_);
v_k_3491_ = lean_ctor_get(v_lr_3481_, 1);
lean_inc(v_k_3491_);
v_v_3492_ = lean_ctor_get(v_lr_3481_, 2);
lean_inc(v_v_3492_);
v_l_3493_ = lean_ctor_get(v_lr_3481_, 3);
lean_inc(v_l_3493_);
v_r_3494_ = lean_ctor_get(v_lr_3481_, 4);
lean_inc(v_r_3494_);
lean_dec_ref(v_lr_3481_);
v___x_3495_ = lean_apply_10(v_h__1_3482_, v_size_3485_, v_k_3486_, v_v_3487_, v_l_3488_, v_r_3489_, v_size_3490_, v_k_3491_, v_v_3492_, v_l_3493_, v_r_3494_);
return v___x_3495_;
}
else
{
lean_object* v_size_3496_; lean_object* v_k_3497_; lean_object* v_v_3498_; lean_object* v_l_3499_; lean_object* v_r_3500_; lean_object* v___x_3501_; 
lean_dec(v_h__1_3482_);
v_size_3496_ = lean_ctor_get(v_ll_3480_, 0);
lean_inc(v_size_3496_);
v_k_3497_ = lean_ctor_get(v_ll_3480_, 1);
lean_inc(v_k_3497_);
v_v_3498_ = lean_ctor_get(v_ll_3480_, 2);
lean_inc(v_v_3498_);
v_l_3499_ = lean_ctor_get(v_ll_3480_, 3);
lean_inc(v_l_3499_);
v_r_3500_ = lean_ctor_get(v_ll_3480_, 4);
lean_inc(v_r_3500_);
lean_dec_ref(v_ll_3480_);
v___x_3501_ = lean_apply_5(v_h__2_3483_, v_size_3496_, v_k_3497_, v_v_3498_, v_l_3499_, v_r_3500_);
return v___x_3501_;
}
}
else
{
lean_object* v___x_3502_; 
lean_dec(v_h__2_3483_);
lean_dec(v_h__1_3482_);
v___x_3502_ = lean_apply_1(v_h__3_3484_, v_lr_3481_);
return v___x_3502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__3_splitter(lean_object* v_00_u03b1_3503_, lean_object* v_00_u03b2_3504_, lean_object* v_motive_3505_, lean_object* v_ll_3506_, lean_object* v_lr_3507_, lean_object* v_h__1_3508_, lean_object* v_h__2_3509_, lean_object* v_h__3_3510_){
_start:
{
if (lean_obj_tag(v_ll_3506_) == 0)
{
lean_dec(v_h__3_3510_);
if (lean_obj_tag(v_lr_3507_) == 0)
{
lean_object* v_size_3511_; lean_object* v_k_3512_; lean_object* v_v_3513_; lean_object* v_l_3514_; lean_object* v_r_3515_; lean_object* v_size_3516_; lean_object* v_k_3517_; lean_object* v_v_3518_; lean_object* v_l_3519_; lean_object* v_r_3520_; lean_object* v___x_3521_; 
lean_dec(v_h__2_3509_);
v_size_3511_ = lean_ctor_get(v_ll_3506_, 0);
lean_inc(v_size_3511_);
v_k_3512_ = lean_ctor_get(v_ll_3506_, 1);
lean_inc(v_k_3512_);
v_v_3513_ = lean_ctor_get(v_ll_3506_, 2);
lean_inc(v_v_3513_);
v_l_3514_ = lean_ctor_get(v_ll_3506_, 3);
lean_inc(v_l_3514_);
v_r_3515_ = lean_ctor_get(v_ll_3506_, 4);
lean_inc(v_r_3515_);
lean_dec_ref(v_ll_3506_);
v_size_3516_ = lean_ctor_get(v_lr_3507_, 0);
lean_inc(v_size_3516_);
v_k_3517_ = lean_ctor_get(v_lr_3507_, 1);
lean_inc(v_k_3517_);
v_v_3518_ = lean_ctor_get(v_lr_3507_, 2);
lean_inc(v_v_3518_);
v_l_3519_ = lean_ctor_get(v_lr_3507_, 3);
lean_inc(v_l_3519_);
v_r_3520_ = lean_ctor_get(v_lr_3507_, 4);
lean_inc(v_r_3520_);
lean_dec_ref(v_lr_3507_);
v___x_3521_ = lean_apply_10(v_h__1_3508_, v_size_3511_, v_k_3512_, v_v_3513_, v_l_3514_, v_r_3515_, v_size_3516_, v_k_3517_, v_v_3518_, v_l_3519_, v_r_3520_);
return v___x_3521_;
}
else
{
lean_object* v_size_3522_; lean_object* v_k_3523_; lean_object* v_v_3524_; lean_object* v_l_3525_; lean_object* v_r_3526_; lean_object* v___x_3527_; 
lean_dec(v_h__1_3508_);
v_size_3522_ = lean_ctor_get(v_ll_3506_, 0);
lean_inc(v_size_3522_);
v_k_3523_ = lean_ctor_get(v_ll_3506_, 1);
lean_inc(v_k_3523_);
v_v_3524_ = lean_ctor_get(v_ll_3506_, 2);
lean_inc(v_v_3524_);
v_l_3525_ = lean_ctor_get(v_ll_3506_, 3);
lean_inc(v_l_3525_);
v_r_3526_ = lean_ctor_get(v_ll_3506_, 4);
lean_inc(v_r_3526_);
lean_dec_ref(v_ll_3506_);
v___x_3527_ = lean_apply_5(v_h__2_3509_, v_size_3522_, v_k_3523_, v_v_3524_, v_l_3525_, v_r_3526_);
return v___x_3527_;
}
}
else
{
lean_object* v___x_3528_; 
lean_dec(v_h__2_3509_);
lean_dec(v_h__1_3508_);
v___x_3528_ = lean_apply_1(v_h__3_3510_, v_lr_3507_);
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___redArg(lean_object* v_r_3529_, lean_object* v_h__1_3530_, lean_object* v_h__2_3531_){
_start:
{
if (lean_obj_tag(v_r_3529_) == 0)
{
lean_object* v_size_3532_; lean_object* v_k_3533_; lean_object* v_v_3534_; lean_object* v_l_3535_; lean_object* v_r_3536_; lean_object* v___x_3537_; 
lean_dec(v_h__1_3530_);
v_size_3532_ = lean_ctor_get(v_r_3529_, 0);
lean_inc(v_size_3532_);
v_k_3533_ = lean_ctor_get(v_r_3529_, 1);
lean_inc(v_k_3533_);
v_v_3534_ = lean_ctor_get(v_r_3529_, 2);
lean_inc(v_v_3534_);
v_l_3535_ = lean_ctor_get(v_r_3529_, 3);
lean_inc(v_l_3535_);
v_r_3536_ = lean_ctor_get(v_r_3529_, 4);
lean_inc(v_r_3536_);
lean_dec_ref(v_r_3529_);
v___x_3537_ = lean_apply_7(v_h__2_3531_, v_size_3532_, v_k_3533_, v_v_3534_, v_l_3535_, v_r_3536_, lean_box(0), lean_box(0));
return v___x_3537_;
}
else
{
lean_object* v___x_3538_; 
lean_dec(v_h__2_3531_);
v___x_3538_ = lean_apply_2(v_h__1_3530_, lean_box(0), lean_box(0));
return v___x_3538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter(lean_object* v_00_u03b1_3539_, lean_object* v_00_u03b2_3540_, lean_object* v_l_3541_, lean_object* v_motive_3542_, lean_object* v_r_3543_, lean_object* v_hrb_3544_, lean_object* v_hlr_3545_, lean_object* v_h__1_3546_, lean_object* v_h__2_3547_){
_start:
{
if (lean_obj_tag(v_r_3543_) == 0)
{
lean_object* v_size_3548_; lean_object* v_k_3549_; lean_object* v_v_3550_; lean_object* v_l_3551_; lean_object* v_r_3552_; lean_object* v___x_3553_; 
lean_dec(v_h__1_3546_);
v_size_3548_ = lean_ctor_get(v_r_3543_, 0);
lean_inc(v_size_3548_);
v_k_3549_ = lean_ctor_get(v_r_3543_, 1);
lean_inc(v_k_3549_);
v_v_3550_ = lean_ctor_get(v_r_3543_, 2);
lean_inc(v_v_3550_);
v_l_3551_ = lean_ctor_get(v_r_3543_, 3);
lean_inc(v_l_3551_);
v_r_3552_ = lean_ctor_get(v_r_3543_, 4);
lean_inc(v_r_3552_);
lean_dec_ref(v_r_3543_);
v___x_3553_ = lean_apply_7(v_h__2_3547_, v_size_3548_, v_k_3549_, v_v_3550_, v_l_3551_, v_r_3552_, lean_box(0), lean_box(0));
return v___x_3553_;
}
else
{
lean_object* v___x_3554_; 
lean_dec(v_h__2_3547_);
v___x_3554_ = lean_apply_2(v_h__1_3546_, lean_box(0), lean_box(0));
return v___x_3554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter___boxed(lean_object* v_00_u03b1_3555_, lean_object* v_00_u03b2_3556_, lean_object* v_l_3557_, lean_object* v_motive_3558_, lean_object* v_r_3559_, lean_object* v_hrb_3560_, lean_object* v_hlr_3561_, lean_object* v_h__1_3562_, lean_object* v_h__2_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__7_splitter(v_00_u03b1_3555_, v_00_u03b2_3556_, v_l_3557_, v_motive_3558_, v_r_3559_, v_hrb_3560_, v_hlr_3561_, v_h__1_3562_, v_h__2_3563_);
lean_dec(v_l_3557_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter___redArg(lean_object* v_l_3565_, lean_object* v_h__1_3566_, lean_object* v_h__2_3567_, lean_object* v_h__3_3568_, lean_object* v_h__4_3569_, lean_object* v_h__5_3570_){
_start:
{
if (lean_obj_tag(v_l_3565_) == 0)
{
lean_object* v_l_3571_; 
lean_dec(v_h__1_3566_);
v_l_3571_ = lean_ctor_get(v_l_3565_, 3);
if (lean_obj_tag(v_l_3571_) == 0)
{
lean_object* v_r_3572_; 
lean_inc_ref(v_l_3571_);
lean_dec(v_h__3_3568_);
lean_dec(v_h__2_3567_);
v_r_3572_ = lean_ctor_get(v_l_3565_, 4);
if (lean_obj_tag(v_r_3572_) == 0)
{
lean_object* v_size_3573_; lean_object* v_k_3574_; lean_object* v_v_3575_; lean_object* v_size_3576_; lean_object* v_k_3577_; lean_object* v_v_3578_; lean_object* v_l_3579_; lean_object* v_r_3580_; lean_object* v_size_3581_; lean_object* v_k_3582_; lean_object* v_v_3583_; lean_object* v_l_3584_; lean_object* v_r_3585_; lean_object* v___x_3586_; 
lean_inc_ref(v_r_3572_);
lean_dec(v_h__4_3569_);
v_size_3573_ = lean_ctor_get(v_l_3565_, 0);
lean_inc(v_size_3573_);
v_k_3574_ = lean_ctor_get(v_l_3565_, 1);
lean_inc(v_k_3574_);
v_v_3575_ = lean_ctor_get(v_l_3565_, 2);
lean_inc(v_v_3575_);
lean_dec_ref(v_l_3565_);
v_size_3576_ = lean_ctor_get(v_l_3571_, 0);
lean_inc(v_size_3576_);
v_k_3577_ = lean_ctor_get(v_l_3571_, 1);
lean_inc(v_k_3577_);
v_v_3578_ = lean_ctor_get(v_l_3571_, 2);
lean_inc(v_v_3578_);
v_l_3579_ = lean_ctor_get(v_l_3571_, 3);
lean_inc(v_l_3579_);
v_r_3580_ = lean_ctor_get(v_l_3571_, 4);
lean_inc(v_r_3580_);
lean_dec_ref(v_l_3571_);
v_size_3581_ = lean_ctor_get(v_r_3572_, 0);
lean_inc(v_size_3581_);
v_k_3582_ = lean_ctor_get(v_r_3572_, 1);
lean_inc(v_k_3582_);
v_v_3583_ = lean_ctor_get(v_r_3572_, 2);
lean_inc(v_v_3583_);
v_l_3584_ = lean_ctor_get(v_r_3572_, 3);
lean_inc(v_l_3584_);
v_r_3585_ = lean_ctor_get(v_r_3572_, 4);
lean_inc(v_r_3585_);
lean_dec_ref(v_r_3572_);
v___x_3586_ = lean_apply_15(v_h__5_3570_, v_size_3573_, v_k_3574_, v_v_3575_, v_size_3576_, v_k_3577_, v_v_3578_, v_l_3579_, v_r_3580_, v_size_3581_, v_k_3582_, v_v_3583_, v_l_3584_, v_r_3585_, lean_box(0), lean_box(0));
return v___x_3586_;
}
else
{
lean_object* v_size_3587_; lean_object* v_k_3588_; lean_object* v_v_3589_; lean_object* v_size_3590_; lean_object* v_k_3591_; lean_object* v_v_3592_; lean_object* v_l_3593_; lean_object* v_r_3594_; lean_object* v___x_3595_; 
lean_dec(v_h__5_3570_);
v_size_3587_ = lean_ctor_get(v_l_3565_, 0);
lean_inc(v_size_3587_);
v_k_3588_ = lean_ctor_get(v_l_3565_, 1);
lean_inc(v_k_3588_);
v_v_3589_ = lean_ctor_get(v_l_3565_, 2);
lean_inc(v_v_3589_);
lean_dec_ref(v_l_3565_);
v_size_3590_ = lean_ctor_get(v_l_3571_, 0);
lean_inc(v_size_3590_);
v_k_3591_ = lean_ctor_get(v_l_3571_, 1);
lean_inc(v_k_3591_);
v_v_3592_ = lean_ctor_get(v_l_3571_, 2);
lean_inc(v_v_3592_);
v_l_3593_ = lean_ctor_get(v_l_3571_, 3);
lean_inc(v_l_3593_);
v_r_3594_ = lean_ctor_get(v_l_3571_, 4);
lean_inc(v_r_3594_);
lean_dec_ref(v_l_3571_);
v___x_3595_ = lean_apply_10(v_h__4_3569_, v_size_3587_, v_k_3588_, v_v_3589_, v_size_3590_, v_k_3591_, v_v_3592_, v_l_3593_, v_r_3594_, lean_box(0), lean_box(0));
return v___x_3595_;
}
}
else
{
lean_object* v_r_3596_; 
lean_dec(v_h__5_3570_);
lean_dec(v_h__4_3569_);
v_r_3596_ = lean_ctor_get(v_l_3565_, 4);
if (lean_obj_tag(v_r_3596_) == 0)
{
lean_object* v_size_3597_; lean_object* v_k_3598_; lean_object* v_v_3599_; lean_object* v_size_3600_; lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v_l_3603_; lean_object* v_r_3604_; lean_object* v___x_3605_; 
lean_inc_ref(v_r_3596_);
lean_dec(v_h__2_3567_);
v_size_3597_ = lean_ctor_get(v_l_3565_, 0);
lean_inc(v_size_3597_);
v_k_3598_ = lean_ctor_get(v_l_3565_, 1);
lean_inc(v_k_3598_);
v_v_3599_ = lean_ctor_get(v_l_3565_, 2);
lean_inc(v_v_3599_);
lean_dec_ref(v_l_3565_);
v_size_3600_ = lean_ctor_get(v_r_3596_, 0);
lean_inc(v_size_3600_);
v_k_3601_ = lean_ctor_get(v_r_3596_, 1);
lean_inc(v_k_3601_);
v_v_3602_ = lean_ctor_get(v_r_3596_, 2);
lean_inc(v_v_3602_);
v_l_3603_ = lean_ctor_get(v_r_3596_, 3);
lean_inc(v_l_3603_);
v_r_3604_ = lean_ctor_get(v_r_3596_, 4);
lean_inc(v_r_3604_);
lean_dec_ref(v_r_3596_);
v___x_3605_ = lean_apply_10(v_h__3_3568_, v_size_3597_, v_k_3598_, v_v_3599_, v_size_3600_, v_k_3601_, v_v_3602_, v_l_3603_, v_r_3604_, lean_box(0), lean_box(0));
return v___x_3605_;
}
else
{
lean_object* v_size_3606_; lean_object* v_k_3607_; lean_object* v_v_3608_; lean_object* v___x_3609_; 
lean_dec(v_h__3_3568_);
v_size_3606_ = lean_ctor_get(v_l_3565_, 0);
lean_inc(v_size_3606_);
v_k_3607_ = lean_ctor_get(v_l_3565_, 1);
lean_inc(v_k_3607_);
v_v_3608_ = lean_ctor_get(v_l_3565_, 2);
lean_inc(v_v_3608_);
lean_dec_ref(v_l_3565_);
v___x_3609_ = lean_apply_5(v_h__2_3567_, v_size_3606_, v_k_3607_, v_v_3608_, lean_box(0), lean_box(0));
return v___x_3609_;
}
}
}
else
{
lean_object* v___x_3610_; 
lean_dec(v_h__5_3570_);
lean_dec(v_h__4_3569_);
lean_dec(v_h__3_3568_);
lean_dec(v_h__2_3567_);
v___x_3610_ = lean_apply_2(v_h__1_3566_, lean_box(0), lean_box(0));
return v___x_3610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__1_splitter(lean_object* v_00_u03b1_3611_, lean_object* v_00_u03b2_3612_, lean_object* v_motive_3613_, lean_object* v_l_3614_, lean_object* v_hlb_3615_, lean_object* v_hlr_3616_, lean_object* v_h__1_3617_, lean_object* v_h__2_3618_, lean_object* v_h__3_3619_, lean_object* v_h__4_3620_, lean_object* v_h__5_3621_){
_start:
{
if (lean_obj_tag(v_l_3614_) == 0)
{
lean_object* v_l_3622_; 
lean_dec(v_h__1_3617_);
v_l_3622_ = lean_ctor_get(v_l_3614_, 3);
if (lean_obj_tag(v_l_3622_) == 0)
{
lean_object* v_r_3623_; 
lean_inc_ref(v_l_3622_);
lean_dec(v_h__3_3619_);
lean_dec(v_h__2_3618_);
v_r_3623_ = lean_ctor_get(v_l_3614_, 4);
if (lean_obj_tag(v_r_3623_) == 0)
{
lean_object* v_size_3624_; lean_object* v_k_3625_; lean_object* v_v_3626_; lean_object* v_size_3627_; lean_object* v_k_3628_; lean_object* v_v_3629_; lean_object* v_l_3630_; lean_object* v_r_3631_; lean_object* v_size_3632_; lean_object* v_k_3633_; lean_object* v_v_3634_; lean_object* v_l_3635_; lean_object* v_r_3636_; lean_object* v___x_3637_; 
lean_inc_ref(v_r_3623_);
lean_dec(v_h__4_3620_);
v_size_3624_ = lean_ctor_get(v_l_3614_, 0);
lean_inc(v_size_3624_);
v_k_3625_ = lean_ctor_get(v_l_3614_, 1);
lean_inc(v_k_3625_);
v_v_3626_ = lean_ctor_get(v_l_3614_, 2);
lean_inc(v_v_3626_);
lean_dec_ref(v_l_3614_);
v_size_3627_ = lean_ctor_get(v_l_3622_, 0);
lean_inc(v_size_3627_);
v_k_3628_ = lean_ctor_get(v_l_3622_, 1);
lean_inc(v_k_3628_);
v_v_3629_ = lean_ctor_get(v_l_3622_, 2);
lean_inc(v_v_3629_);
v_l_3630_ = lean_ctor_get(v_l_3622_, 3);
lean_inc(v_l_3630_);
v_r_3631_ = lean_ctor_get(v_l_3622_, 4);
lean_inc(v_r_3631_);
lean_dec_ref(v_l_3622_);
v_size_3632_ = lean_ctor_get(v_r_3623_, 0);
lean_inc(v_size_3632_);
v_k_3633_ = lean_ctor_get(v_r_3623_, 1);
lean_inc(v_k_3633_);
v_v_3634_ = lean_ctor_get(v_r_3623_, 2);
lean_inc(v_v_3634_);
v_l_3635_ = lean_ctor_get(v_r_3623_, 3);
lean_inc(v_l_3635_);
v_r_3636_ = lean_ctor_get(v_r_3623_, 4);
lean_inc(v_r_3636_);
lean_dec_ref(v_r_3623_);
v___x_3637_ = lean_apply_15(v_h__5_3621_, v_size_3624_, v_k_3625_, v_v_3626_, v_size_3627_, v_k_3628_, v_v_3629_, v_l_3630_, v_r_3631_, v_size_3632_, v_k_3633_, v_v_3634_, v_l_3635_, v_r_3636_, lean_box(0), lean_box(0));
return v___x_3637_;
}
else
{
lean_object* v_size_3638_; lean_object* v_k_3639_; lean_object* v_v_3640_; lean_object* v_size_3641_; lean_object* v_k_3642_; lean_object* v_v_3643_; lean_object* v_l_3644_; lean_object* v_r_3645_; lean_object* v___x_3646_; 
lean_dec(v_h__5_3621_);
v_size_3638_ = lean_ctor_get(v_l_3614_, 0);
lean_inc(v_size_3638_);
v_k_3639_ = lean_ctor_get(v_l_3614_, 1);
lean_inc(v_k_3639_);
v_v_3640_ = lean_ctor_get(v_l_3614_, 2);
lean_inc(v_v_3640_);
lean_dec_ref(v_l_3614_);
v_size_3641_ = lean_ctor_get(v_l_3622_, 0);
lean_inc(v_size_3641_);
v_k_3642_ = lean_ctor_get(v_l_3622_, 1);
lean_inc(v_k_3642_);
v_v_3643_ = lean_ctor_get(v_l_3622_, 2);
lean_inc(v_v_3643_);
v_l_3644_ = lean_ctor_get(v_l_3622_, 3);
lean_inc(v_l_3644_);
v_r_3645_ = lean_ctor_get(v_l_3622_, 4);
lean_inc(v_r_3645_);
lean_dec_ref(v_l_3622_);
v___x_3646_ = lean_apply_10(v_h__4_3620_, v_size_3638_, v_k_3639_, v_v_3640_, v_size_3641_, v_k_3642_, v_v_3643_, v_l_3644_, v_r_3645_, lean_box(0), lean_box(0));
return v___x_3646_;
}
}
else
{
lean_object* v_r_3647_; 
lean_dec(v_h__5_3621_);
lean_dec(v_h__4_3620_);
v_r_3647_ = lean_ctor_get(v_l_3614_, 4);
if (lean_obj_tag(v_r_3647_) == 0)
{
lean_object* v_size_3648_; lean_object* v_k_3649_; lean_object* v_v_3650_; lean_object* v_size_3651_; lean_object* v_k_3652_; lean_object* v_v_3653_; lean_object* v_l_3654_; lean_object* v_r_3655_; lean_object* v___x_3656_; 
lean_inc_ref(v_r_3647_);
lean_dec(v_h__2_3618_);
v_size_3648_ = lean_ctor_get(v_l_3614_, 0);
lean_inc(v_size_3648_);
v_k_3649_ = lean_ctor_get(v_l_3614_, 1);
lean_inc(v_k_3649_);
v_v_3650_ = lean_ctor_get(v_l_3614_, 2);
lean_inc(v_v_3650_);
lean_dec_ref(v_l_3614_);
v_size_3651_ = lean_ctor_get(v_r_3647_, 0);
lean_inc(v_size_3651_);
v_k_3652_ = lean_ctor_get(v_r_3647_, 1);
lean_inc(v_k_3652_);
v_v_3653_ = lean_ctor_get(v_r_3647_, 2);
lean_inc(v_v_3653_);
v_l_3654_ = lean_ctor_get(v_r_3647_, 3);
lean_inc(v_l_3654_);
v_r_3655_ = lean_ctor_get(v_r_3647_, 4);
lean_inc(v_r_3655_);
lean_dec_ref(v_r_3647_);
v___x_3656_ = lean_apply_10(v_h__3_3619_, v_size_3648_, v_k_3649_, v_v_3650_, v_size_3651_, v_k_3652_, v_v_3653_, v_l_3654_, v_r_3655_, lean_box(0), lean_box(0));
return v___x_3656_;
}
else
{
lean_object* v_size_3657_; lean_object* v_k_3658_; lean_object* v_v_3659_; lean_object* v___x_3660_; 
lean_dec(v_h__3_3619_);
v_size_3657_ = lean_ctor_get(v_l_3614_, 0);
lean_inc(v_size_3657_);
v_k_3658_ = lean_ctor_get(v_l_3614_, 1);
lean_inc(v_k_3658_);
v_v_3659_ = lean_ctor_get(v_l_3614_, 2);
lean_inc(v_v_3659_);
lean_dec_ref(v_l_3614_);
v___x_3660_ = lean_apply_5(v_h__2_3618_, v_size_3657_, v_k_3658_, v_v_3659_, lean_box(0), lean_box(0));
return v___x_3660_;
}
}
}
else
{
lean_object* v___x_3661_; 
lean_dec(v_h__5_3621_);
lean_dec(v_h__4_3620_);
lean_dec(v_h__3_3619_);
lean_dec(v_h__2_3618_);
v___x_3661_ = lean_apply_2(v_h__1_3617_, lean_box(0), lean_box(0));
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___redArg(lean_object* v_l_3662_, lean_object* v_h__1_3663_, lean_object* v_h__2_3664_){
_start:
{
if (lean_obj_tag(v_l_3662_) == 0)
{
lean_object* v_size_3665_; lean_object* v_k_3666_; lean_object* v_v_3667_; lean_object* v_l_3668_; lean_object* v_r_3669_; lean_object* v___x_3670_; 
lean_dec(v_h__1_3663_);
v_size_3665_ = lean_ctor_get(v_l_3662_, 0);
lean_inc(v_size_3665_);
v_k_3666_ = lean_ctor_get(v_l_3662_, 1);
lean_inc(v_k_3666_);
v_v_3667_ = lean_ctor_get(v_l_3662_, 2);
lean_inc(v_v_3667_);
v_l_3668_ = lean_ctor_get(v_l_3662_, 3);
lean_inc(v_l_3668_);
v_r_3669_ = lean_ctor_get(v_l_3662_, 4);
lean_inc(v_r_3669_);
lean_dec_ref(v_l_3662_);
v___x_3670_ = lean_apply_7(v_h__2_3664_, v_size_3665_, v_k_3666_, v_v_3667_, v_l_3668_, v_r_3669_, lean_box(0), lean_box(0));
return v___x_3670_;
}
else
{
lean_object* v___x_3671_; 
lean_dec(v_h__2_3664_);
v___x_3671_ = lean_apply_2(v_h__1_3663_, lean_box(0), lean_box(0));
return v___x_3671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter(lean_object* v_00_u03b1_3672_, lean_object* v_00_u03b2_3673_, lean_object* v_rs_3674_, lean_object* v_k_3675_, lean_object* v_v_3676_, lean_object* v_l_3677_, lean_object* v_r_3678_, lean_object* v_motive_3679_, lean_object* v_l_3680_, lean_object* v_hlb_3681_, lean_object* v_hlr_3682_, lean_object* v_h__1_3683_, lean_object* v_h__2_3684_){
_start:
{
if (lean_obj_tag(v_l_3680_) == 0)
{
lean_object* v_size_3685_; lean_object* v_k_3686_; lean_object* v_v_3687_; lean_object* v_l_3688_; lean_object* v_r_3689_; lean_object* v___x_3690_; 
lean_dec(v_h__1_3683_);
v_size_3685_ = lean_ctor_get(v_l_3680_, 0);
lean_inc(v_size_3685_);
v_k_3686_ = lean_ctor_get(v_l_3680_, 1);
lean_inc(v_k_3686_);
v_v_3687_ = lean_ctor_get(v_l_3680_, 2);
lean_inc(v_v_3687_);
v_l_3688_ = lean_ctor_get(v_l_3680_, 3);
lean_inc(v_l_3688_);
v_r_3689_ = lean_ctor_get(v_l_3680_, 4);
lean_inc(v_r_3689_);
lean_dec_ref(v_l_3680_);
v___x_3690_ = lean_apply_7(v_h__2_3684_, v_size_3685_, v_k_3686_, v_v_3687_, v_l_3688_, v_r_3689_, lean_box(0), lean_box(0));
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; 
lean_dec(v_h__2_3684_);
v___x_3691_ = lean_apply_2(v_h__1_3683_, lean_box(0), lean_box(0));
return v___x_3691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter___boxed(lean_object* v_00_u03b1_3692_, lean_object* v_00_u03b2_3693_, lean_object* v_rs_3694_, lean_object* v_k_3695_, lean_object* v_v_3696_, lean_object* v_l_3697_, lean_object* v_r_3698_, lean_object* v_motive_3699_, lean_object* v_l_3700_, lean_object* v_hlb_3701_, lean_object* v_hlr_3702_, lean_object* v_h__1_3703_, lean_object* v_h__2_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__5_splitter(v_00_u03b1_3692_, v_00_u03b2_3693_, v_rs_3694_, v_k_3695_, v_v_3696_, v_l_3697_, v_r_3698_, v_motive_3699_, v_l_3700_, v_hlb_3701_, v_hlr_3702_, v_h__1_3703_, v_h__2_3704_);
lean_dec(v_r_3698_);
lean_dec(v_l_3697_);
lean_dec(v_v_3696_);
lean_dec(v_k_3695_);
lean_dec(v_rs_3694_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___redArg(lean_object* v_ll_3706_, lean_object* v_lr_3707_, lean_object* v_h__1_3708_, lean_object* v_h__2_3709_, lean_object* v_h__3_3710_){
_start:
{
if (lean_obj_tag(v_ll_3706_) == 0)
{
lean_dec(v_h__3_3710_);
if (lean_obj_tag(v_lr_3707_) == 0)
{
lean_object* v_size_3711_; lean_object* v_k_3712_; lean_object* v_v_3713_; lean_object* v_l_3714_; lean_object* v_r_3715_; lean_object* v_size_3716_; lean_object* v_k_3717_; lean_object* v_v_3718_; lean_object* v_l_3719_; lean_object* v_r_3720_; lean_object* v___x_3721_; 
lean_dec(v_h__2_3709_);
v_size_3711_ = lean_ctor_get(v_ll_3706_, 0);
lean_inc(v_size_3711_);
v_k_3712_ = lean_ctor_get(v_ll_3706_, 1);
lean_inc(v_k_3712_);
v_v_3713_ = lean_ctor_get(v_ll_3706_, 2);
lean_inc(v_v_3713_);
v_l_3714_ = lean_ctor_get(v_ll_3706_, 3);
lean_inc(v_l_3714_);
v_r_3715_ = lean_ctor_get(v_ll_3706_, 4);
lean_inc(v_r_3715_);
lean_dec_ref(v_ll_3706_);
v_size_3716_ = lean_ctor_get(v_lr_3707_, 0);
lean_inc(v_size_3716_);
v_k_3717_ = lean_ctor_get(v_lr_3707_, 1);
lean_inc(v_k_3717_);
v_v_3718_ = lean_ctor_get(v_lr_3707_, 2);
lean_inc(v_v_3718_);
v_l_3719_ = lean_ctor_get(v_lr_3707_, 3);
lean_inc(v_l_3719_);
v_r_3720_ = lean_ctor_get(v_lr_3707_, 4);
lean_inc(v_r_3720_);
lean_dec_ref(v_lr_3707_);
v___x_3721_ = lean_apply_12(v_h__1_3708_, v_size_3711_, v_k_3712_, v_v_3713_, v_l_3714_, v_r_3715_, v_size_3716_, v_k_3717_, v_v_3718_, v_l_3719_, v_r_3720_, lean_box(0), lean_box(0));
return v___x_3721_;
}
else
{
lean_object* v_size_3722_; lean_object* v_k_3723_; lean_object* v_v_3724_; lean_object* v_l_3725_; lean_object* v_r_3726_; lean_object* v___x_3727_; 
lean_dec(v_h__1_3708_);
v_size_3722_ = lean_ctor_get(v_ll_3706_, 0);
lean_inc(v_size_3722_);
v_k_3723_ = lean_ctor_get(v_ll_3706_, 1);
lean_inc(v_k_3723_);
v_v_3724_ = lean_ctor_get(v_ll_3706_, 2);
lean_inc(v_v_3724_);
v_l_3725_ = lean_ctor_get(v_ll_3706_, 3);
lean_inc(v_l_3725_);
v_r_3726_ = lean_ctor_get(v_ll_3706_, 4);
lean_inc(v_r_3726_);
lean_dec_ref(v_ll_3706_);
v___x_3727_ = lean_apply_7(v_h__2_3709_, v_size_3722_, v_k_3723_, v_v_3724_, v_l_3725_, v_r_3726_, lean_box(0), lean_box(0));
return v___x_3727_;
}
}
else
{
lean_object* v___x_3728_; 
lean_dec(v_h__2_3709_);
lean_dec(v_h__1_3708_);
v___x_3728_ = lean_apply_3(v_h__3_3710_, v_lr_3707_, lean_box(0), lean_box(0));
return v___x_3728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter(lean_object* v_00_u03b1_3729_, lean_object* v_00_u03b2_3730_, lean_object* v_rs_3731_, lean_object* v_k_3732_, lean_object* v_v_3733_, lean_object* v_l_3734_, lean_object* v_r_3735_, lean_object* v_ls_3736_, lean_object* v_lk_3737_, lean_object* v_lv_3738_, lean_object* v_motive_3739_, lean_object* v_ll_3740_, lean_object* v_lr_3741_, lean_object* v_hlb_3742_, lean_object* v_hlr_3743_, lean_object* v_h__1_3744_, lean_object* v_h__2_3745_, lean_object* v_h__3_3746_){
_start:
{
if (lean_obj_tag(v_ll_3740_) == 0)
{
lean_dec(v_h__3_3746_);
if (lean_obj_tag(v_lr_3741_) == 0)
{
lean_object* v_size_3747_; lean_object* v_k_3748_; lean_object* v_v_3749_; lean_object* v_l_3750_; lean_object* v_r_3751_; lean_object* v_size_3752_; lean_object* v_k_3753_; lean_object* v_v_3754_; lean_object* v_l_3755_; lean_object* v_r_3756_; lean_object* v___x_3757_; 
lean_dec(v_h__2_3745_);
v_size_3747_ = lean_ctor_get(v_ll_3740_, 0);
lean_inc(v_size_3747_);
v_k_3748_ = lean_ctor_get(v_ll_3740_, 1);
lean_inc(v_k_3748_);
v_v_3749_ = lean_ctor_get(v_ll_3740_, 2);
lean_inc(v_v_3749_);
v_l_3750_ = lean_ctor_get(v_ll_3740_, 3);
lean_inc(v_l_3750_);
v_r_3751_ = lean_ctor_get(v_ll_3740_, 4);
lean_inc(v_r_3751_);
lean_dec_ref(v_ll_3740_);
v_size_3752_ = lean_ctor_get(v_lr_3741_, 0);
lean_inc(v_size_3752_);
v_k_3753_ = lean_ctor_get(v_lr_3741_, 1);
lean_inc(v_k_3753_);
v_v_3754_ = lean_ctor_get(v_lr_3741_, 2);
lean_inc(v_v_3754_);
v_l_3755_ = lean_ctor_get(v_lr_3741_, 3);
lean_inc(v_l_3755_);
v_r_3756_ = lean_ctor_get(v_lr_3741_, 4);
lean_inc(v_r_3756_);
lean_dec_ref(v_lr_3741_);
v___x_3757_ = lean_apply_12(v_h__1_3744_, v_size_3747_, v_k_3748_, v_v_3749_, v_l_3750_, v_r_3751_, v_size_3752_, v_k_3753_, v_v_3754_, v_l_3755_, v_r_3756_, lean_box(0), lean_box(0));
return v___x_3757_;
}
else
{
lean_object* v_size_3758_; lean_object* v_k_3759_; lean_object* v_v_3760_; lean_object* v_l_3761_; lean_object* v_r_3762_; lean_object* v___x_3763_; 
lean_dec(v_h__1_3744_);
v_size_3758_ = lean_ctor_get(v_ll_3740_, 0);
lean_inc(v_size_3758_);
v_k_3759_ = lean_ctor_get(v_ll_3740_, 1);
lean_inc(v_k_3759_);
v_v_3760_ = lean_ctor_get(v_ll_3740_, 2);
lean_inc(v_v_3760_);
v_l_3761_ = lean_ctor_get(v_ll_3740_, 3);
lean_inc(v_l_3761_);
v_r_3762_ = lean_ctor_get(v_ll_3740_, 4);
lean_inc(v_r_3762_);
lean_dec_ref(v_ll_3740_);
v___x_3763_ = lean_apply_7(v_h__2_3745_, v_size_3758_, v_k_3759_, v_v_3760_, v_l_3761_, v_r_3762_, lean_box(0), lean_box(0));
return v___x_3763_;
}
}
else
{
lean_object* v___x_3764_; 
lean_dec(v_h__2_3745_);
lean_dec(v_h__1_3744_);
v___x_3764_ = lean_apply_3(v_h__3_3746_, v_lr_3741_, lean_box(0), lean_box(0));
return v___x_3764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter___boxed(lean_object** _args){
lean_object* v_00_u03b1_3765_ = _args[0];
lean_object* v_00_u03b2_3766_ = _args[1];
lean_object* v_rs_3767_ = _args[2];
lean_object* v_k_3768_ = _args[3];
lean_object* v_v_3769_ = _args[4];
lean_object* v_l_3770_ = _args[5];
lean_object* v_r_3771_ = _args[6];
lean_object* v_ls_3772_ = _args[7];
lean_object* v_lk_3773_ = _args[8];
lean_object* v_lv_3774_ = _args[9];
lean_object* v_motive_3775_ = _args[10];
lean_object* v_ll_3776_ = _args[11];
lean_object* v_lr_3777_ = _args[12];
lean_object* v_hlb_3778_ = _args[13];
lean_object* v_hlr_3779_ = _args[14];
lean_object* v_h__1_3780_ = _args[15];
lean_object* v_h__2_3781_ = _args[16];
lean_object* v_h__3_3782_ = _args[17];
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_match__3_splitter(v_00_u03b1_3765_, v_00_u03b2_3766_, v_rs_3767_, v_k_3768_, v_v_3769_, v_l_3770_, v_r_3771_, v_ls_3772_, v_lk_3773_, v_lv_3774_, v_motive_3775_, v_ll_3776_, v_lr_3777_, v_hlb_3778_, v_hlr_3779_, v_h__1_3780_, v_h__2_3781_, v_h__3_3782_);
lean_dec(v_lv_3774_);
lean_dec(v_lk_3773_);
lean_dec(v_ls_3772_);
lean_dec(v_r_3771_);
lean_dec(v_l_3770_);
lean_dec(v_v_3769_);
lean_dec(v_k_3768_);
lean_dec(v_rs_3767_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter___redArg(lean_object* v_l_3784_, lean_object* v_h__1_3785_, lean_object* v_h__2_3786_, lean_object* v_h__3_3787_, lean_object* v_h__4_3788_, lean_object* v_h__5_3789_){
_start:
{
if (lean_obj_tag(v_l_3784_) == 0)
{
lean_object* v_l_3790_; 
lean_dec(v_h__1_3785_);
v_l_3790_ = lean_ctor_get(v_l_3784_, 3);
if (lean_obj_tag(v_l_3790_) == 0)
{
lean_object* v_r_3791_; 
lean_inc_ref(v_l_3790_);
lean_dec(v_h__3_3787_);
lean_dec(v_h__2_3786_);
v_r_3791_ = lean_ctor_get(v_l_3784_, 4);
if (lean_obj_tag(v_r_3791_) == 0)
{
lean_object* v_size_3792_; lean_object* v_k_3793_; lean_object* v_v_3794_; lean_object* v_size_3795_; lean_object* v_k_3796_; lean_object* v_v_3797_; lean_object* v_l_3798_; lean_object* v_r_3799_; lean_object* v_size_3800_; lean_object* v_k_3801_; lean_object* v_v_3802_; lean_object* v_l_3803_; lean_object* v_r_3804_; lean_object* v___x_3805_; 
lean_inc_ref(v_r_3791_);
lean_dec(v_h__4_3788_);
v_size_3792_ = lean_ctor_get(v_l_3784_, 0);
lean_inc(v_size_3792_);
v_k_3793_ = lean_ctor_get(v_l_3784_, 1);
lean_inc(v_k_3793_);
v_v_3794_ = lean_ctor_get(v_l_3784_, 2);
lean_inc(v_v_3794_);
lean_dec_ref(v_l_3784_);
v_size_3795_ = lean_ctor_get(v_l_3790_, 0);
lean_inc(v_size_3795_);
v_k_3796_ = lean_ctor_get(v_l_3790_, 1);
lean_inc(v_k_3796_);
v_v_3797_ = lean_ctor_get(v_l_3790_, 2);
lean_inc(v_v_3797_);
v_l_3798_ = lean_ctor_get(v_l_3790_, 3);
lean_inc(v_l_3798_);
v_r_3799_ = lean_ctor_get(v_l_3790_, 4);
lean_inc(v_r_3799_);
lean_dec_ref(v_l_3790_);
v_size_3800_ = lean_ctor_get(v_r_3791_, 0);
lean_inc(v_size_3800_);
v_k_3801_ = lean_ctor_get(v_r_3791_, 1);
lean_inc(v_k_3801_);
v_v_3802_ = lean_ctor_get(v_r_3791_, 2);
lean_inc(v_v_3802_);
v_l_3803_ = lean_ctor_get(v_r_3791_, 3);
lean_inc(v_l_3803_);
v_r_3804_ = lean_ctor_get(v_r_3791_, 4);
lean_inc(v_r_3804_);
lean_dec_ref(v_r_3791_);
v___x_3805_ = lean_apply_13(v_h__5_3789_, v_size_3792_, v_k_3793_, v_v_3794_, v_size_3795_, v_k_3796_, v_v_3797_, v_l_3798_, v_r_3799_, v_size_3800_, v_k_3801_, v_v_3802_, v_l_3803_, v_r_3804_);
return v___x_3805_;
}
else
{
lean_object* v_size_3806_; lean_object* v_k_3807_; lean_object* v_v_3808_; lean_object* v_size_3809_; lean_object* v_k_3810_; lean_object* v_v_3811_; lean_object* v_l_3812_; lean_object* v_r_3813_; lean_object* v___x_3814_; 
lean_dec(v_h__5_3789_);
v_size_3806_ = lean_ctor_get(v_l_3784_, 0);
lean_inc(v_size_3806_);
v_k_3807_ = lean_ctor_get(v_l_3784_, 1);
lean_inc(v_k_3807_);
v_v_3808_ = lean_ctor_get(v_l_3784_, 2);
lean_inc(v_v_3808_);
lean_dec_ref(v_l_3784_);
v_size_3809_ = lean_ctor_get(v_l_3790_, 0);
lean_inc(v_size_3809_);
v_k_3810_ = lean_ctor_get(v_l_3790_, 1);
lean_inc(v_k_3810_);
v_v_3811_ = lean_ctor_get(v_l_3790_, 2);
lean_inc(v_v_3811_);
v_l_3812_ = lean_ctor_get(v_l_3790_, 3);
lean_inc(v_l_3812_);
v_r_3813_ = lean_ctor_get(v_l_3790_, 4);
lean_inc(v_r_3813_);
lean_dec_ref(v_l_3790_);
v___x_3814_ = lean_apply_8(v_h__4_3788_, v_size_3806_, v_k_3807_, v_v_3808_, v_size_3809_, v_k_3810_, v_v_3811_, v_l_3812_, v_r_3813_);
return v___x_3814_;
}
}
else
{
lean_object* v_r_3815_; 
lean_dec(v_h__5_3789_);
lean_dec(v_h__4_3788_);
v_r_3815_ = lean_ctor_get(v_l_3784_, 4);
if (lean_obj_tag(v_r_3815_) == 0)
{
lean_object* v_size_3816_; lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v_size_3819_; lean_object* v_k_3820_; lean_object* v_v_3821_; lean_object* v_l_3822_; lean_object* v_r_3823_; lean_object* v___x_3824_; 
lean_inc_ref(v_r_3815_);
lean_dec(v_h__2_3786_);
v_size_3816_ = lean_ctor_get(v_l_3784_, 0);
lean_inc(v_size_3816_);
v_k_3817_ = lean_ctor_get(v_l_3784_, 1);
lean_inc(v_k_3817_);
v_v_3818_ = lean_ctor_get(v_l_3784_, 2);
lean_inc(v_v_3818_);
lean_dec_ref(v_l_3784_);
v_size_3819_ = lean_ctor_get(v_r_3815_, 0);
lean_inc(v_size_3819_);
v_k_3820_ = lean_ctor_get(v_r_3815_, 1);
lean_inc(v_k_3820_);
v_v_3821_ = lean_ctor_get(v_r_3815_, 2);
lean_inc(v_v_3821_);
v_l_3822_ = lean_ctor_get(v_r_3815_, 3);
lean_inc(v_l_3822_);
v_r_3823_ = lean_ctor_get(v_r_3815_, 4);
lean_inc(v_r_3823_);
lean_dec_ref(v_r_3815_);
v___x_3824_ = lean_apply_8(v_h__3_3787_, v_size_3816_, v_k_3817_, v_v_3818_, v_size_3819_, v_k_3820_, v_v_3821_, v_l_3822_, v_r_3823_);
return v___x_3824_;
}
else
{
lean_object* v_size_3825_; lean_object* v_k_3826_; lean_object* v_v_3827_; lean_object* v___x_3828_; 
lean_dec(v_h__3_3787_);
v_size_3825_ = lean_ctor_get(v_l_3784_, 0);
lean_inc(v_size_3825_);
v_k_3826_ = lean_ctor_get(v_l_3784_, 1);
lean_inc(v_k_3826_);
v_v_3827_ = lean_ctor_get(v_l_3784_, 2);
lean_inc(v_v_3827_);
lean_dec_ref(v_l_3784_);
v___x_3828_ = lean_apply_3(v_h__2_3786_, v_size_3825_, v_k_3826_, v_v_3827_);
return v___x_3828_;
}
}
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec(v_h__5_3789_);
lean_dec(v_h__4_3788_);
lean_dec(v_h__3_3787_);
lean_dec(v_h__2_3786_);
v___x_3829_ = lean_box(0);
v___x_3830_ = lean_apply_1(v_h__1_3785_, v___x_3829_);
return v___x_3830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceL_x21_match__1_splitter(lean_object* v_00_u03b1_3831_, lean_object* v_00_u03b2_3832_, lean_object* v_motive_3833_, lean_object* v_l_3834_, lean_object* v_h__1_3835_, lean_object* v_h__2_3836_, lean_object* v_h__3_3837_, lean_object* v_h__4_3838_, lean_object* v_h__5_3839_){
_start:
{
if (lean_obj_tag(v_l_3834_) == 0)
{
lean_object* v_l_3840_; 
lean_dec(v_h__1_3835_);
v_l_3840_ = lean_ctor_get(v_l_3834_, 3);
if (lean_obj_tag(v_l_3840_) == 0)
{
lean_object* v_r_3841_; 
lean_inc_ref(v_l_3840_);
lean_dec(v_h__3_3837_);
lean_dec(v_h__2_3836_);
v_r_3841_ = lean_ctor_get(v_l_3834_, 4);
if (lean_obj_tag(v_r_3841_) == 0)
{
lean_object* v_size_3842_; lean_object* v_k_3843_; lean_object* v_v_3844_; lean_object* v_size_3845_; lean_object* v_k_3846_; lean_object* v_v_3847_; lean_object* v_l_3848_; lean_object* v_r_3849_; lean_object* v_size_3850_; lean_object* v_k_3851_; lean_object* v_v_3852_; lean_object* v_l_3853_; lean_object* v_r_3854_; lean_object* v___x_3855_; 
lean_inc_ref(v_r_3841_);
lean_dec(v_h__4_3838_);
v_size_3842_ = lean_ctor_get(v_l_3834_, 0);
lean_inc(v_size_3842_);
v_k_3843_ = lean_ctor_get(v_l_3834_, 1);
lean_inc(v_k_3843_);
v_v_3844_ = lean_ctor_get(v_l_3834_, 2);
lean_inc(v_v_3844_);
lean_dec_ref(v_l_3834_);
v_size_3845_ = lean_ctor_get(v_l_3840_, 0);
lean_inc(v_size_3845_);
v_k_3846_ = lean_ctor_get(v_l_3840_, 1);
lean_inc(v_k_3846_);
v_v_3847_ = lean_ctor_get(v_l_3840_, 2);
lean_inc(v_v_3847_);
v_l_3848_ = lean_ctor_get(v_l_3840_, 3);
lean_inc(v_l_3848_);
v_r_3849_ = lean_ctor_get(v_l_3840_, 4);
lean_inc(v_r_3849_);
lean_dec_ref(v_l_3840_);
v_size_3850_ = lean_ctor_get(v_r_3841_, 0);
lean_inc(v_size_3850_);
v_k_3851_ = lean_ctor_get(v_r_3841_, 1);
lean_inc(v_k_3851_);
v_v_3852_ = lean_ctor_get(v_r_3841_, 2);
lean_inc(v_v_3852_);
v_l_3853_ = lean_ctor_get(v_r_3841_, 3);
lean_inc(v_l_3853_);
v_r_3854_ = lean_ctor_get(v_r_3841_, 4);
lean_inc(v_r_3854_);
lean_dec_ref(v_r_3841_);
v___x_3855_ = lean_apply_13(v_h__5_3839_, v_size_3842_, v_k_3843_, v_v_3844_, v_size_3845_, v_k_3846_, v_v_3847_, v_l_3848_, v_r_3849_, v_size_3850_, v_k_3851_, v_v_3852_, v_l_3853_, v_r_3854_);
return v___x_3855_;
}
else
{
lean_object* v_size_3856_; lean_object* v_k_3857_; lean_object* v_v_3858_; lean_object* v_size_3859_; lean_object* v_k_3860_; lean_object* v_v_3861_; lean_object* v_l_3862_; lean_object* v_r_3863_; lean_object* v___x_3864_; 
lean_dec(v_h__5_3839_);
v_size_3856_ = lean_ctor_get(v_l_3834_, 0);
lean_inc(v_size_3856_);
v_k_3857_ = lean_ctor_get(v_l_3834_, 1);
lean_inc(v_k_3857_);
v_v_3858_ = lean_ctor_get(v_l_3834_, 2);
lean_inc(v_v_3858_);
lean_dec_ref(v_l_3834_);
v_size_3859_ = lean_ctor_get(v_l_3840_, 0);
lean_inc(v_size_3859_);
v_k_3860_ = lean_ctor_get(v_l_3840_, 1);
lean_inc(v_k_3860_);
v_v_3861_ = lean_ctor_get(v_l_3840_, 2);
lean_inc(v_v_3861_);
v_l_3862_ = lean_ctor_get(v_l_3840_, 3);
lean_inc(v_l_3862_);
v_r_3863_ = lean_ctor_get(v_l_3840_, 4);
lean_inc(v_r_3863_);
lean_dec_ref(v_l_3840_);
v___x_3864_ = lean_apply_8(v_h__4_3838_, v_size_3856_, v_k_3857_, v_v_3858_, v_size_3859_, v_k_3860_, v_v_3861_, v_l_3862_, v_r_3863_);
return v___x_3864_;
}
}
else
{
lean_object* v_r_3865_; 
lean_dec(v_h__5_3839_);
lean_dec(v_h__4_3838_);
v_r_3865_ = lean_ctor_get(v_l_3834_, 4);
if (lean_obj_tag(v_r_3865_) == 0)
{
lean_object* v_size_3866_; lean_object* v_k_3867_; lean_object* v_v_3868_; lean_object* v_size_3869_; lean_object* v_k_3870_; lean_object* v_v_3871_; lean_object* v_l_3872_; lean_object* v_r_3873_; lean_object* v___x_3874_; 
lean_inc_ref(v_r_3865_);
lean_dec(v_h__2_3836_);
v_size_3866_ = lean_ctor_get(v_l_3834_, 0);
lean_inc(v_size_3866_);
v_k_3867_ = lean_ctor_get(v_l_3834_, 1);
lean_inc(v_k_3867_);
v_v_3868_ = lean_ctor_get(v_l_3834_, 2);
lean_inc(v_v_3868_);
lean_dec_ref(v_l_3834_);
v_size_3869_ = lean_ctor_get(v_r_3865_, 0);
lean_inc(v_size_3869_);
v_k_3870_ = lean_ctor_get(v_r_3865_, 1);
lean_inc(v_k_3870_);
v_v_3871_ = lean_ctor_get(v_r_3865_, 2);
lean_inc(v_v_3871_);
v_l_3872_ = lean_ctor_get(v_r_3865_, 3);
lean_inc(v_l_3872_);
v_r_3873_ = lean_ctor_get(v_r_3865_, 4);
lean_inc(v_r_3873_);
lean_dec_ref(v_r_3865_);
v___x_3874_ = lean_apply_8(v_h__3_3837_, v_size_3866_, v_k_3867_, v_v_3868_, v_size_3869_, v_k_3870_, v_v_3871_, v_l_3872_, v_r_3873_);
return v___x_3874_;
}
else
{
lean_object* v_size_3875_; lean_object* v_k_3876_; lean_object* v_v_3877_; lean_object* v___x_3878_; 
lean_dec(v_h__3_3837_);
v_size_3875_ = lean_ctor_get(v_l_3834_, 0);
lean_inc(v_size_3875_);
v_k_3876_ = lean_ctor_get(v_l_3834_, 1);
lean_inc(v_k_3876_);
v_v_3877_ = lean_ctor_get(v_l_3834_, 2);
lean_inc(v_v_3877_);
lean_dec_ref(v_l_3834_);
v___x_3878_ = lean_apply_3(v_h__2_3836_, v_size_3875_, v_k_3876_, v_v_3877_);
return v___x_3878_;
}
}
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_dec(v_h__5_3839_);
lean_dec(v_h__4_3838_);
lean_dec(v_h__3_3837_);
lean_dec(v_h__2_3836_);
v___x_3879_ = lean_box(0);
v___x_3880_ = lean_apply_1(v_h__1_3835_, v___x_3879_);
return v___x_3880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___redArg(lean_object* v_ll_3881_, lean_object* v_lr_3882_, lean_object* v_h__1_3883_, lean_object* v_h__2_3884_, lean_object* v_h__3_3885_){
_start:
{
if (lean_obj_tag(v_ll_3881_) == 0)
{
lean_dec(v_h__3_3885_);
if (lean_obj_tag(v_lr_3882_) == 0)
{
lean_object* v_size_3886_; lean_object* v_k_3887_; lean_object* v_v_3888_; lean_object* v_l_3889_; lean_object* v_r_3890_; lean_object* v_size_3891_; lean_object* v_k_3892_; lean_object* v_v_3893_; lean_object* v_l_3894_; lean_object* v_r_3895_; lean_object* v___x_3896_; 
lean_dec(v_h__2_3884_);
v_size_3886_ = lean_ctor_get(v_ll_3881_, 0);
lean_inc(v_size_3886_);
v_k_3887_ = lean_ctor_get(v_ll_3881_, 1);
lean_inc(v_k_3887_);
v_v_3888_ = lean_ctor_get(v_ll_3881_, 2);
lean_inc(v_v_3888_);
v_l_3889_ = lean_ctor_get(v_ll_3881_, 3);
lean_inc(v_l_3889_);
v_r_3890_ = lean_ctor_get(v_ll_3881_, 4);
lean_inc(v_r_3890_);
lean_dec_ref(v_ll_3881_);
v_size_3891_ = lean_ctor_get(v_lr_3882_, 0);
lean_inc(v_size_3891_);
v_k_3892_ = lean_ctor_get(v_lr_3882_, 1);
lean_inc(v_k_3892_);
v_v_3893_ = lean_ctor_get(v_lr_3882_, 2);
lean_inc(v_v_3893_);
v_l_3894_ = lean_ctor_get(v_lr_3882_, 3);
lean_inc(v_l_3894_);
v_r_3895_ = lean_ctor_get(v_lr_3882_, 4);
lean_inc(v_r_3895_);
lean_dec_ref(v_lr_3882_);
v___x_3896_ = lean_apply_12(v_h__1_3883_, v_size_3886_, v_k_3887_, v_v_3888_, v_l_3889_, v_r_3890_, v_size_3891_, v_k_3892_, v_v_3893_, v_l_3894_, v_r_3895_, lean_box(0), lean_box(0));
return v___x_3896_;
}
else
{
lean_object* v_size_3897_; lean_object* v_k_3898_; lean_object* v_v_3899_; lean_object* v_l_3900_; lean_object* v_r_3901_; lean_object* v___x_3902_; 
lean_dec(v_h__1_3883_);
v_size_3897_ = lean_ctor_get(v_ll_3881_, 0);
lean_inc(v_size_3897_);
v_k_3898_ = lean_ctor_get(v_ll_3881_, 1);
lean_inc(v_k_3898_);
v_v_3899_ = lean_ctor_get(v_ll_3881_, 2);
lean_inc(v_v_3899_);
v_l_3900_ = lean_ctor_get(v_ll_3881_, 3);
lean_inc(v_l_3900_);
v_r_3901_ = lean_ctor_get(v_ll_3881_, 4);
lean_inc(v_r_3901_);
lean_dec_ref(v_ll_3881_);
v___x_3902_ = lean_apply_7(v_h__2_3884_, v_size_3897_, v_k_3898_, v_v_3899_, v_l_3900_, v_r_3901_, lean_box(0), lean_box(0));
return v___x_3902_;
}
}
else
{
lean_object* v___x_3903_; 
lean_dec(v_h__2_3884_);
lean_dec(v_h__1_3883_);
v___x_3903_ = lean_apply_3(v_h__3_3885_, v_lr_3882_, lean_box(0), lean_box(0));
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter(lean_object* v_00_u03b1_3904_, lean_object* v_00_u03b2_3905_, lean_object* v_rs_3906_, lean_object* v_k_3907_, lean_object* v_v_3908_, lean_object* v_l_3909_, lean_object* v_r_3910_, lean_object* v_ls_3911_, lean_object* v_lk_3912_, lean_object* v_lv_3913_, lean_object* v_motive_3914_, lean_object* v_ll_3915_, lean_object* v_lr_3916_, lean_object* v_hlb_3917_, lean_object* v_hlr_3918_, lean_object* v_h__1_3919_, lean_object* v_h__2_3920_, lean_object* v_h__3_3921_){
_start:
{
if (lean_obj_tag(v_ll_3915_) == 0)
{
lean_dec(v_h__3_3921_);
if (lean_obj_tag(v_lr_3916_) == 0)
{
lean_object* v_size_3922_; lean_object* v_k_3923_; lean_object* v_v_3924_; lean_object* v_l_3925_; lean_object* v_r_3926_; lean_object* v_size_3927_; lean_object* v_k_3928_; lean_object* v_v_3929_; lean_object* v_l_3930_; lean_object* v_r_3931_; lean_object* v___x_3932_; 
lean_dec(v_h__2_3920_);
v_size_3922_ = lean_ctor_get(v_ll_3915_, 0);
lean_inc(v_size_3922_);
v_k_3923_ = lean_ctor_get(v_ll_3915_, 1);
lean_inc(v_k_3923_);
v_v_3924_ = lean_ctor_get(v_ll_3915_, 2);
lean_inc(v_v_3924_);
v_l_3925_ = lean_ctor_get(v_ll_3915_, 3);
lean_inc(v_l_3925_);
v_r_3926_ = lean_ctor_get(v_ll_3915_, 4);
lean_inc(v_r_3926_);
lean_dec_ref(v_ll_3915_);
v_size_3927_ = lean_ctor_get(v_lr_3916_, 0);
lean_inc(v_size_3927_);
v_k_3928_ = lean_ctor_get(v_lr_3916_, 1);
lean_inc(v_k_3928_);
v_v_3929_ = lean_ctor_get(v_lr_3916_, 2);
lean_inc(v_v_3929_);
v_l_3930_ = lean_ctor_get(v_lr_3916_, 3);
lean_inc(v_l_3930_);
v_r_3931_ = lean_ctor_get(v_lr_3916_, 4);
lean_inc(v_r_3931_);
lean_dec_ref(v_lr_3916_);
v___x_3932_ = lean_apply_12(v_h__1_3919_, v_size_3922_, v_k_3923_, v_v_3924_, v_l_3925_, v_r_3926_, v_size_3927_, v_k_3928_, v_v_3929_, v_l_3930_, v_r_3931_, lean_box(0), lean_box(0));
return v___x_3932_;
}
else
{
lean_object* v_size_3933_; lean_object* v_k_3934_; lean_object* v_v_3935_; lean_object* v_l_3936_; lean_object* v_r_3937_; lean_object* v___x_3938_; 
lean_dec(v_h__1_3919_);
v_size_3933_ = lean_ctor_get(v_ll_3915_, 0);
lean_inc(v_size_3933_);
v_k_3934_ = lean_ctor_get(v_ll_3915_, 1);
lean_inc(v_k_3934_);
v_v_3935_ = lean_ctor_get(v_ll_3915_, 2);
lean_inc(v_v_3935_);
v_l_3936_ = lean_ctor_get(v_ll_3915_, 3);
lean_inc(v_l_3936_);
v_r_3937_ = lean_ctor_get(v_ll_3915_, 4);
lean_inc(v_r_3937_);
lean_dec_ref(v_ll_3915_);
v___x_3938_ = lean_apply_7(v_h__2_3920_, v_size_3933_, v_k_3934_, v_v_3935_, v_l_3936_, v_r_3937_, lean_box(0), lean_box(0));
return v___x_3938_;
}
}
else
{
lean_object* v___x_3939_; 
lean_dec(v_h__2_3920_);
lean_dec(v_h__1_3919_);
v___x_3939_ = lean_apply_3(v_h__3_3921_, v_lr_3916_, lean_box(0), lean_box(0));
return v___x_3939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter___boxed(lean_object** _args){
lean_object* v_00_u03b1_3940_ = _args[0];
lean_object* v_00_u03b2_3941_ = _args[1];
lean_object* v_rs_3942_ = _args[2];
lean_object* v_k_3943_ = _args[3];
lean_object* v_v_3944_ = _args[4];
lean_object* v_l_3945_ = _args[5];
lean_object* v_r_3946_ = _args[6];
lean_object* v_ls_3947_ = _args[7];
lean_object* v_lk_3948_ = _args[8];
lean_object* v_lv_3949_ = _args[9];
lean_object* v_motive_3950_ = _args[10];
lean_object* v_ll_3951_ = _args[11];
lean_object* v_lr_3952_ = _args[12];
lean_object* v_hlb_3953_ = _args[13];
lean_object* v_hlr_3954_ = _args[14];
lean_object* v_h__1_3955_ = _args[15];
lean_object* v_h__2_3956_ = _args[16];
lean_object* v_h__3_3957_ = _args[17];
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__3_splitter(v_00_u03b1_3940_, v_00_u03b2_3941_, v_rs_3942_, v_k_3943_, v_v_3944_, v_l_3945_, v_r_3946_, v_ls_3947_, v_lk_3948_, v_lv_3949_, v_motive_3950_, v_ll_3951_, v_lr_3952_, v_hlb_3953_, v_hlr_3954_, v_h__1_3955_, v_h__2_3956_, v_h__3_3957_);
lean_dec(v_lv_3949_);
lean_dec(v_lk_3948_);
lean_dec(v_ls_3947_);
lean_dec(v_r_3946_);
lean_dec(v_l_3945_);
lean_dec(v_v_3944_);
lean_dec(v_k_3943_);
lean_dec(v_rs_3942_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter___redArg(lean_object* v_r_3959_, lean_object* v_h__1_3960_, lean_object* v_h__2_3961_, lean_object* v_h__3_3962_, lean_object* v_h__4_3963_, lean_object* v_h__5_3964_){
_start:
{
if (lean_obj_tag(v_r_3959_) == 0)
{
lean_object* v_l_3965_; 
lean_dec(v_h__1_3960_);
v_l_3965_ = lean_ctor_get(v_r_3959_, 3);
if (lean_obj_tag(v_l_3965_) == 0)
{
lean_object* v_r_3966_; 
lean_inc_ref(v_l_3965_);
lean_dec(v_h__3_3962_);
lean_dec(v_h__2_3961_);
v_r_3966_ = lean_ctor_get(v_r_3959_, 4);
if (lean_obj_tag(v_r_3966_) == 0)
{
lean_object* v_size_3967_; lean_object* v_k_3968_; lean_object* v_v_3969_; lean_object* v_size_3970_; lean_object* v_k_3971_; lean_object* v_v_3972_; lean_object* v_l_3973_; lean_object* v_r_3974_; lean_object* v_size_3975_; lean_object* v_k_3976_; lean_object* v_v_3977_; lean_object* v_l_3978_; lean_object* v_r_3979_; lean_object* v___x_3980_; 
lean_inc_ref(v_r_3966_);
lean_dec(v_h__4_3963_);
v_size_3967_ = lean_ctor_get(v_r_3959_, 0);
lean_inc(v_size_3967_);
v_k_3968_ = lean_ctor_get(v_r_3959_, 1);
lean_inc(v_k_3968_);
v_v_3969_ = lean_ctor_get(v_r_3959_, 2);
lean_inc(v_v_3969_);
lean_dec_ref(v_r_3959_);
v_size_3970_ = lean_ctor_get(v_l_3965_, 0);
lean_inc(v_size_3970_);
v_k_3971_ = lean_ctor_get(v_l_3965_, 1);
lean_inc(v_k_3971_);
v_v_3972_ = lean_ctor_get(v_l_3965_, 2);
lean_inc(v_v_3972_);
v_l_3973_ = lean_ctor_get(v_l_3965_, 3);
lean_inc(v_l_3973_);
v_r_3974_ = lean_ctor_get(v_l_3965_, 4);
lean_inc(v_r_3974_);
lean_dec_ref(v_l_3965_);
v_size_3975_ = lean_ctor_get(v_r_3966_, 0);
lean_inc(v_size_3975_);
v_k_3976_ = lean_ctor_get(v_r_3966_, 1);
lean_inc(v_k_3976_);
v_v_3977_ = lean_ctor_get(v_r_3966_, 2);
lean_inc(v_v_3977_);
v_l_3978_ = lean_ctor_get(v_r_3966_, 3);
lean_inc(v_l_3978_);
v_r_3979_ = lean_ctor_get(v_r_3966_, 4);
lean_inc(v_r_3979_);
lean_dec_ref(v_r_3966_);
v___x_3980_ = lean_apply_15(v_h__5_3964_, v_size_3967_, v_k_3968_, v_v_3969_, v_size_3970_, v_k_3971_, v_v_3972_, v_l_3973_, v_r_3974_, v_size_3975_, v_k_3976_, v_v_3977_, v_l_3978_, v_r_3979_, lean_box(0), lean_box(0));
return v___x_3980_;
}
else
{
lean_object* v_size_3981_; lean_object* v_k_3982_; lean_object* v_v_3983_; lean_object* v_size_3984_; lean_object* v_k_3985_; lean_object* v_v_3986_; lean_object* v_l_3987_; lean_object* v_r_3988_; lean_object* v___x_3989_; 
lean_dec(v_h__5_3964_);
v_size_3981_ = lean_ctor_get(v_r_3959_, 0);
lean_inc(v_size_3981_);
v_k_3982_ = lean_ctor_get(v_r_3959_, 1);
lean_inc(v_k_3982_);
v_v_3983_ = lean_ctor_get(v_r_3959_, 2);
lean_inc(v_v_3983_);
lean_dec_ref(v_r_3959_);
v_size_3984_ = lean_ctor_get(v_l_3965_, 0);
lean_inc(v_size_3984_);
v_k_3985_ = lean_ctor_get(v_l_3965_, 1);
lean_inc(v_k_3985_);
v_v_3986_ = lean_ctor_get(v_l_3965_, 2);
lean_inc(v_v_3986_);
v_l_3987_ = lean_ctor_get(v_l_3965_, 3);
lean_inc(v_l_3987_);
v_r_3988_ = lean_ctor_get(v_l_3965_, 4);
lean_inc(v_r_3988_);
lean_dec_ref(v_l_3965_);
v___x_3989_ = lean_apply_10(v_h__4_3963_, v_size_3981_, v_k_3982_, v_v_3983_, v_size_3984_, v_k_3985_, v_v_3986_, v_l_3987_, v_r_3988_, lean_box(0), lean_box(0));
return v___x_3989_;
}
}
else
{
lean_object* v_r_3990_; 
lean_dec(v_h__5_3964_);
lean_dec(v_h__4_3963_);
v_r_3990_ = lean_ctor_get(v_r_3959_, 4);
if (lean_obj_tag(v_r_3990_) == 0)
{
lean_object* v_size_3991_; lean_object* v_k_3992_; lean_object* v_v_3993_; lean_object* v_size_3994_; lean_object* v_k_3995_; lean_object* v_v_3996_; lean_object* v_l_3997_; lean_object* v_r_3998_; lean_object* v___x_3999_; 
lean_inc_ref(v_r_3990_);
lean_dec(v_h__2_3961_);
v_size_3991_ = lean_ctor_get(v_r_3959_, 0);
lean_inc(v_size_3991_);
v_k_3992_ = lean_ctor_get(v_r_3959_, 1);
lean_inc(v_k_3992_);
v_v_3993_ = lean_ctor_get(v_r_3959_, 2);
lean_inc(v_v_3993_);
lean_dec_ref(v_r_3959_);
v_size_3994_ = lean_ctor_get(v_r_3990_, 0);
lean_inc(v_size_3994_);
v_k_3995_ = lean_ctor_get(v_r_3990_, 1);
lean_inc(v_k_3995_);
v_v_3996_ = lean_ctor_get(v_r_3990_, 2);
lean_inc(v_v_3996_);
v_l_3997_ = lean_ctor_get(v_r_3990_, 3);
lean_inc(v_l_3997_);
v_r_3998_ = lean_ctor_get(v_r_3990_, 4);
lean_inc(v_r_3998_);
lean_dec_ref(v_r_3990_);
v___x_3999_ = lean_apply_10(v_h__3_3962_, v_size_3991_, v_k_3992_, v_v_3993_, v_size_3994_, v_k_3995_, v_v_3996_, v_l_3997_, v_r_3998_, lean_box(0), lean_box(0));
return v___x_3999_;
}
else
{
lean_object* v_size_4000_; lean_object* v_k_4001_; lean_object* v_v_4002_; lean_object* v___x_4003_; 
lean_dec(v_h__3_3962_);
v_size_4000_ = lean_ctor_get(v_r_3959_, 0);
lean_inc(v_size_4000_);
v_k_4001_ = lean_ctor_get(v_r_3959_, 1);
lean_inc(v_k_4001_);
v_v_4002_ = lean_ctor_get(v_r_3959_, 2);
lean_inc(v_v_4002_);
lean_dec_ref(v_r_3959_);
v___x_4003_ = lean_apply_5(v_h__2_3961_, v_size_4000_, v_k_4001_, v_v_4002_, lean_box(0), lean_box(0));
return v___x_4003_;
}
}
}
else
{
lean_object* v___x_4004_; 
lean_dec(v_h__5_3964_);
lean_dec(v_h__4_3963_);
lean_dec(v_h__3_3962_);
lean_dec(v_h__2_3961_);
v___x_4004_ = lean_apply_2(v_h__1_3960_, lean_box(0), lean_box(0));
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_match__1_splitter(lean_object* v_00_u03b1_4005_, lean_object* v_00_u03b2_4006_, lean_object* v_motive_4007_, lean_object* v_r_4008_, lean_object* v_hrb_4009_, lean_object* v_hlr_4010_, lean_object* v_h__1_4011_, lean_object* v_h__2_4012_, lean_object* v_h__3_4013_, lean_object* v_h__4_4014_, lean_object* v_h__5_4015_){
_start:
{
if (lean_obj_tag(v_r_4008_) == 0)
{
lean_object* v_l_4016_; 
lean_dec(v_h__1_4011_);
v_l_4016_ = lean_ctor_get(v_r_4008_, 3);
if (lean_obj_tag(v_l_4016_) == 0)
{
lean_object* v_r_4017_; 
lean_inc_ref(v_l_4016_);
lean_dec(v_h__3_4013_);
lean_dec(v_h__2_4012_);
v_r_4017_ = lean_ctor_get(v_r_4008_, 4);
if (lean_obj_tag(v_r_4017_) == 0)
{
lean_object* v_size_4018_; lean_object* v_k_4019_; lean_object* v_v_4020_; lean_object* v_size_4021_; lean_object* v_k_4022_; lean_object* v_v_4023_; lean_object* v_l_4024_; lean_object* v_r_4025_; lean_object* v_size_4026_; lean_object* v_k_4027_; lean_object* v_v_4028_; lean_object* v_l_4029_; lean_object* v_r_4030_; lean_object* v___x_4031_; 
lean_inc_ref(v_r_4017_);
lean_dec(v_h__4_4014_);
v_size_4018_ = lean_ctor_get(v_r_4008_, 0);
lean_inc(v_size_4018_);
v_k_4019_ = lean_ctor_get(v_r_4008_, 1);
lean_inc(v_k_4019_);
v_v_4020_ = lean_ctor_get(v_r_4008_, 2);
lean_inc(v_v_4020_);
lean_dec_ref(v_r_4008_);
v_size_4021_ = lean_ctor_get(v_l_4016_, 0);
lean_inc(v_size_4021_);
v_k_4022_ = lean_ctor_get(v_l_4016_, 1);
lean_inc(v_k_4022_);
v_v_4023_ = lean_ctor_get(v_l_4016_, 2);
lean_inc(v_v_4023_);
v_l_4024_ = lean_ctor_get(v_l_4016_, 3);
lean_inc(v_l_4024_);
v_r_4025_ = lean_ctor_get(v_l_4016_, 4);
lean_inc(v_r_4025_);
lean_dec_ref(v_l_4016_);
v_size_4026_ = lean_ctor_get(v_r_4017_, 0);
lean_inc(v_size_4026_);
v_k_4027_ = lean_ctor_get(v_r_4017_, 1);
lean_inc(v_k_4027_);
v_v_4028_ = lean_ctor_get(v_r_4017_, 2);
lean_inc(v_v_4028_);
v_l_4029_ = lean_ctor_get(v_r_4017_, 3);
lean_inc(v_l_4029_);
v_r_4030_ = lean_ctor_get(v_r_4017_, 4);
lean_inc(v_r_4030_);
lean_dec_ref(v_r_4017_);
v___x_4031_ = lean_apply_15(v_h__5_4015_, v_size_4018_, v_k_4019_, v_v_4020_, v_size_4021_, v_k_4022_, v_v_4023_, v_l_4024_, v_r_4025_, v_size_4026_, v_k_4027_, v_v_4028_, v_l_4029_, v_r_4030_, lean_box(0), lean_box(0));
return v___x_4031_;
}
else
{
lean_object* v_size_4032_; lean_object* v_k_4033_; lean_object* v_v_4034_; lean_object* v_size_4035_; lean_object* v_k_4036_; lean_object* v_v_4037_; lean_object* v_l_4038_; lean_object* v_r_4039_; lean_object* v___x_4040_; 
lean_dec(v_h__5_4015_);
v_size_4032_ = lean_ctor_get(v_r_4008_, 0);
lean_inc(v_size_4032_);
v_k_4033_ = lean_ctor_get(v_r_4008_, 1);
lean_inc(v_k_4033_);
v_v_4034_ = lean_ctor_get(v_r_4008_, 2);
lean_inc(v_v_4034_);
lean_dec_ref(v_r_4008_);
v_size_4035_ = lean_ctor_get(v_l_4016_, 0);
lean_inc(v_size_4035_);
v_k_4036_ = lean_ctor_get(v_l_4016_, 1);
lean_inc(v_k_4036_);
v_v_4037_ = lean_ctor_get(v_l_4016_, 2);
lean_inc(v_v_4037_);
v_l_4038_ = lean_ctor_get(v_l_4016_, 3);
lean_inc(v_l_4038_);
v_r_4039_ = lean_ctor_get(v_l_4016_, 4);
lean_inc(v_r_4039_);
lean_dec_ref(v_l_4016_);
v___x_4040_ = lean_apply_10(v_h__4_4014_, v_size_4032_, v_k_4033_, v_v_4034_, v_size_4035_, v_k_4036_, v_v_4037_, v_l_4038_, v_r_4039_, lean_box(0), lean_box(0));
return v___x_4040_;
}
}
else
{
lean_object* v_r_4041_; 
lean_dec(v_h__5_4015_);
lean_dec(v_h__4_4014_);
v_r_4041_ = lean_ctor_get(v_r_4008_, 4);
if (lean_obj_tag(v_r_4041_) == 0)
{
lean_object* v_size_4042_; lean_object* v_k_4043_; lean_object* v_v_4044_; lean_object* v_size_4045_; lean_object* v_k_4046_; lean_object* v_v_4047_; lean_object* v_l_4048_; lean_object* v_r_4049_; lean_object* v___x_4050_; 
lean_inc_ref(v_r_4041_);
lean_dec(v_h__2_4012_);
v_size_4042_ = lean_ctor_get(v_r_4008_, 0);
lean_inc(v_size_4042_);
v_k_4043_ = lean_ctor_get(v_r_4008_, 1);
lean_inc(v_k_4043_);
v_v_4044_ = lean_ctor_get(v_r_4008_, 2);
lean_inc(v_v_4044_);
lean_dec_ref(v_r_4008_);
v_size_4045_ = lean_ctor_get(v_r_4041_, 0);
lean_inc(v_size_4045_);
v_k_4046_ = lean_ctor_get(v_r_4041_, 1);
lean_inc(v_k_4046_);
v_v_4047_ = lean_ctor_get(v_r_4041_, 2);
lean_inc(v_v_4047_);
v_l_4048_ = lean_ctor_get(v_r_4041_, 3);
lean_inc(v_l_4048_);
v_r_4049_ = lean_ctor_get(v_r_4041_, 4);
lean_inc(v_r_4049_);
lean_dec_ref(v_r_4041_);
v___x_4050_ = lean_apply_10(v_h__3_4013_, v_size_4042_, v_k_4043_, v_v_4044_, v_size_4045_, v_k_4046_, v_v_4047_, v_l_4048_, v_r_4049_, lean_box(0), lean_box(0));
return v___x_4050_;
}
else
{
lean_object* v_size_4051_; lean_object* v_k_4052_; lean_object* v_v_4053_; lean_object* v___x_4054_; 
lean_dec(v_h__3_4013_);
v_size_4051_ = lean_ctor_get(v_r_4008_, 0);
lean_inc(v_size_4051_);
v_k_4052_ = lean_ctor_get(v_r_4008_, 1);
lean_inc(v_k_4052_);
v_v_4053_ = lean_ctor_get(v_r_4008_, 2);
lean_inc(v_v_4053_);
lean_dec_ref(v_r_4008_);
v___x_4054_ = lean_apply_5(v_h__2_4012_, v_size_4051_, v_k_4052_, v_v_4053_, lean_box(0), lean_box(0));
return v___x_4054_;
}
}
}
else
{
lean_object* v___x_4055_; 
lean_dec(v_h__5_4015_);
lean_dec(v_h__4_4014_);
lean_dec(v_h__3_4013_);
lean_dec(v_h__2_4012_);
v___x_4055_ = lean_apply_2(v_h__1_4011_, lean_box(0), lean_box(0));
return v___x_4055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___redArg(lean_object* v_r_4056_, lean_object* v_h__1_4057_, lean_object* v_h__2_4058_){
_start:
{
if (lean_obj_tag(v_r_4056_) == 0)
{
lean_object* v_size_4059_; lean_object* v_k_4060_; lean_object* v_v_4061_; lean_object* v_l_4062_; lean_object* v_r_4063_; lean_object* v___x_4064_; 
lean_dec(v_h__1_4057_);
v_size_4059_ = lean_ctor_get(v_r_4056_, 0);
lean_inc(v_size_4059_);
v_k_4060_ = lean_ctor_get(v_r_4056_, 1);
lean_inc(v_k_4060_);
v_v_4061_ = lean_ctor_get(v_r_4056_, 2);
lean_inc(v_v_4061_);
v_l_4062_ = lean_ctor_get(v_r_4056_, 3);
lean_inc(v_l_4062_);
v_r_4063_ = lean_ctor_get(v_r_4056_, 4);
lean_inc(v_r_4063_);
lean_dec_ref(v_r_4056_);
v___x_4064_ = lean_apply_7(v_h__2_4058_, v_size_4059_, v_k_4060_, v_v_4061_, v_l_4062_, v_r_4063_, lean_box(0), lean_box(0));
return v___x_4064_;
}
else
{
lean_object* v___x_4065_; 
lean_dec(v_h__2_4058_);
v___x_4065_ = lean_apply_2(v_h__1_4057_, lean_box(0), lean_box(0));
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter(lean_object* v_00_u03b1_4066_, lean_object* v_00_u03b2_4067_, lean_object* v_l_4068_, lean_object* v_motive_4069_, lean_object* v_r_4070_, lean_object* v_hrb_4071_, lean_object* v_hlr_4072_, lean_object* v_h__1_4073_, lean_object* v_h__2_4074_){
_start:
{
if (lean_obj_tag(v_r_4070_) == 0)
{
lean_object* v_size_4075_; lean_object* v_k_4076_; lean_object* v_v_4077_; lean_object* v_l_4078_; lean_object* v_r_4079_; lean_object* v___x_4080_; 
lean_dec(v_h__1_4073_);
v_size_4075_ = lean_ctor_get(v_r_4070_, 0);
lean_inc(v_size_4075_);
v_k_4076_ = lean_ctor_get(v_r_4070_, 1);
lean_inc(v_k_4076_);
v_v_4077_ = lean_ctor_get(v_r_4070_, 2);
lean_inc(v_v_4077_);
v_l_4078_ = lean_ctor_get(v_r_4070_, 3);
lean_inc(v_l_4078_);
v_r_4079_ = lean_ctor_get(v_r_4070_, 4);
lean_inc(v_r_4079_);
lean_dec_ref(v_r_4070_);
v___x_4080_ = lean_apply_7(v_h__2_4074_, v_size_4075_, v_k_4076_, v_v_4077_, v_l_4078_, v_r_4079_, lean_box(0), lean_box(0));
return v___x_4080_;
}
else
{
lean_object* v___x_4081_; 
lean_dec(v_h__2_4074_);
v___x_4081_ = lean_apply_2(v_h__1_4073_, lean_box(0), lean_box(0));
return v___x_4081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter___boxed(lean_object* v_00_u03b1_4082_, lean_object* v_00_u03b2_4083_, lean_object* v_l_4084_, lean_object* v_motive_4085_, lean_object* v_r_4086_, lean_object* v_hrb_4087_, lean_object* v_hlr_4088_, lean_object* v_h__1_4089_, lean_object* v_h__2_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__7_splitter(v_00_u03b1_4082_, v_00_u03b2_4083_, v_l_4084_, v_motive_4085_, v_r_4086_, v_hrb_4087_, v_hlr_4088_, v_h__1_4089_, v_h__2_4090_);
lean_dec(v_l_4084_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter___redArg(lean_object* v_r_4092_, lean_object* v_h__1_4093_, lean_object* v_h__2_4094_, lean_object* v_h__3_4095_, lean_object* v_h__4_4096_, lean_object* v_h__5_4097_){
_start:
{
if (lean_obj_tag(v_r_4092_) == 0)
{
lean_object* v_l_4098_; 
lean_dec(v_h__1_4093_);
v_l_4098_ = lean_ctor_get(v_r_4092_, 3);
if (lean_obj_tag(v_l_4098_) == 0)
{
lean_object* v_r_4099_; 
lean_inc_ref(v_l_4098_);
lean_dec(v_h__3_4095_);
lean_dec(v_h__2_4094_);
v_r_4099_ = lean_ctor_get(v_r_4092_, 4);
if (lean_obj_tag(v_r_4099_) == 0)
{
lean_object* v_size_4100_; lean_object* v_k_4101_; lean_object* v_v_4102_; lean_object* v_size_4103_; lean_object* v_k_4104_; lean_object* v_v_4105_; lean_object* v_l_4106_; lean_object* v_r_4107_; lean_object* v_size_4108_; lean_object* v_k_4109_; lean_object* v_v_4110_; lean_object* v_l_4111_; lean_object* v_r_4112_; lean_object* v___x_4113_; 
lean_inc_ref(v_r_4099_);
lean_dec(v_h__4_4096_);
v_size_4100_ = lean_ctor_get(v_r_4092_, 0);
lean_inc(v_size_4100_);
v_k_4101_ = lean_ctor_get(v_r_4092_, 1);
lean_inc(v_k_4101_);
v_v_4102_ = lean_ctor_get(v_r_4092_, 2);
lean_inc(v_v_4102_);
lean_dec_ref(v_r_4092_);
v_size_4103_ = lean_ctor_get(v_l_4098_, 0);
lean_inc(v_size_4103_);
v_k_4104_ = lean_ctor_get(v_l_4098_, 1);
lean_inc(v_k_4104_);
v_v_4105_ = lean_ctor_get(v_l_4098_, 2);
lean_inc(v_v_4105_);
v_l_4106_ = lean_ctor_get(v_l_4098_, 3);
lean_inc(v_l_4106_);
v_r_4107_ = lean_ctor_get(v_l_4098_, 4);
lean_inc(v_r_4107_);
lean_dec_ref(v_l_4098_);
v_size_4108_ = lean_ctor_get(v_r_4099_, 0);
lean_inc(v_size_4108_);
v_k_4109_ = lean_ctor_get(v_r_4099_, 1);
lean_inc(v_k_4109_);
v_v_4110_ = lean_ctor_get(v_r_4099_, 2);
lean_inc(v_v_4110_);
v_l_4111_ = lean_ctor_get(v_r_4099_, 3);
lean_inc(v_l_4111_);
v_r_4112_ = lean_ctor_get(v_r_4099_, 4);
lean_inc(v_r_4112_);
lean_dec_ref(v_r_4099_);
v___x_4113_ = lean_apply_15(v_h__5_4097_, v_size_4100_, v_k_4101_, v_v_4102_, v_size_4103_, v_k_4104_, v_v_4105_, v_l_4106_, v_r_4107_, v_size_4108_, v_k_4109_, v_v_4110_, v_l_4111_, v_r_4112_, lean_box(0), lean_box(0));
return v___x_4113_;
}
else
{
lean_object* v_size_4114_; lean_object* v_k_4115_; lean_object* v_v_4116_; lean_object* v_size_4117_; lean_object* v_k_4118_; lean_object* v_v_4119_; lean_object* v_l_4120_; lean_object* v_r_4121_; lean_object* v___x_4122_; 
lean_dec(v_h__5_4097_);
v_size_4114_ = lean_ctor_get(v_r_4092_, 0);
lean_inc(v_size_4114_);
v_k_4115_ = lean_ctor_get(v_r_4092_, 1);
lean_inc(v_k_4115_);
v_v_4116_ = lean_ctor_get(v_r_4092_, 2);
lean_inc(v_v_4116_);
lean_dec_ref(v_r_4092_);
v_size_4117_ = lean_ctor_get(v_l_4098_, 0);
lean_inc(v_size_4117_);
v_k_4118_ = lean_ctor_get(v_l_4098_, 1);
lean_inc(v_k_4118_);
v_v_4119_ = lean_ctor_get(v_l_4098_, 2);
lean_inc(v_v_4119_);
v_l_4120_ = lean_ctor_get(v_l_4098_, 3);
lean_inc(v_l_4120_);
v_r_4121_ = lean_ctor_get(v_l_4098_, 4);
lean_inc(v_r_4121_);
lean_dec_ref(v_l_4098_);
v___x_4122_ = lean_apply_10(v_h__4_4096_, v_size_4114_, v_k_4115_, v_v_4116_, v_size_4117_, v_k_4118_, v_v_4119_, v_l_4120_, v_r_4121_, lean_box(0), lean_box(0));
return v___x_4122_;
}
}
else
{
lean_object* v_r_4123_; 
lean_dec(v_h__5_4097_);
lean_dec(v_h__4_4096_);
v_r_4123_ = lean_ctor_get(v_r_4092_, 4);
if (lean_obj_tag(v_r_4123_) == 0)
{
lean_object* v_size_4124_; lean_object* v_k_4125_; lean_object* v_v_4126_; lean_object* v_size_4127_; lean_object* v_k_4128_; lean_object* v_v_4129_; lean_object* v_l_4130_; lean_object* v_r_4131_; lean_object* v___x_4132_; 
lean_inc_ref(v_r_4123_);
lean_dec(v_h__2_4094_);
v_size_4124_ = lean_ctor_get(v_r_4092_, 0);
lean_inc(v_size_4124_);
v_k_4125_ = lean_ctor_get(v_r_4092_, 1);
lean_inc(v_k_4125_);
v_v_4126_ = lean_ctor_get(v_r_4092_, 2);
lean_inc(v_v_4126_);
lean_dec_ref(v_r_4092_);
v_size_4127_ = lean_ctor_get(v_r_4123_, 0);
lean_inc(v_size_4127_);
v_k_4128_ = lean_ctor_get(v_r_4123_, 1);
lean_inc(v_k_4128_);
v_v_4129_ = lean_ctor_get(v_r_4123_, 2);
lean_inc(v_v_4129_);
v_l_4130_ = lean_ctor_get(v_r_4123_, 3);
lean_inc(v_l_4130_);
v_r_4131_ = lean_ctor_get(v_r_4123_, 4);
lean_inc(v_r_4131_);
lean_dec_ref(v_r_4123_);
v___x_4132_ = lean_apply_10(v_h__3_4095_, v_size_4124_, v_k_4125_, v_v_4126_, v_size_4127_, v_k_4128_, v_v_4129_, v_l_4130_, v_r_4131_, lean_box(0), lean_box(0));
return v___x_4132_;
}
else
{
lean_object* v_size_4133_; lean_object* v_k_4134_; lean_object* v_v_4135_; lean_object* v___x_4136_; 
lean_dec(v_h__3_4095_);
v_size_4133_ = lean_ctor_get(v_r_4092_, 0);
lean_inc(v_size_4133_);
v_k_4134_ = lean_ctor_get(v_r_4092_, 1);
lean_inc(v_k_4134_);
v_v_4135_ = lean_ctor_get(v_r_4092_, 2);
lean_inc(v_v_4135_);
lean_dec_ref(v_r_4092_);
v___x_4136_ = lean_apply_5(v_h__2_4094_, v_size_4133_, v_k_4134_, v_v_4135_, lean_box(0), lean_box(0));
return v___x_4136_;
}
}
}
else
{
lean_object* v___x_4137_; 
lean_dec(v_h__5_4097_);
lean_dec(v_h__4_4096_);
lean_dec(v_h__3_4095_);
lean_dec(v_h__2_4094_);
v___x_4137_ = lean_apply_2(v_h__1_4093_, lean_box(0), lean_box(0));
return v___x_4137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceRErase_match__1_splitter(lean_object* v_00_u03b1_4138_, lean_object* v_00_u03b2_4139_, lean_object* v_motive_4140_, lean_object* v_r_4141_, lean_object* v_hrb_4142_, lean_object* v_hlr_4143_, lean_object* v_h__1_4144_, lean_object* v_h__2_4145_, lean_object* v_h__3_4146_, lean_object* v_h__4_4147_, lean_object* v_h__5_4148_){
_start:
{
if (lean_obj_tag(v_r_4141_) == 0)
{
lean_object* v_l_4149_; 
lean_dec(v_h__1_4144_);
v_l_4149_ = lean_ctor_get(v_r_4141_, 3);
if (lean_obj_tag(v_l_4149_) == 0)
{
lean_object* v_r_4150_; 
lean_inc_ref(v_l_4149_);
lean_dec(v_h__3_4146_);
lean_dec(v_h__2_4145_);
v_r_4150_ = lean_ctor_get(v_r_4141_, 4);
if (lean_obj_tag(v_r_4150_) == 0)
{
lean_object* v_size_4151_; lean_object* v_k_4152_; lean_object* v_v_4153_; lean_object* v_size_4154_; lean_object* v_k_4155_; lean_object* v_v_4156_; lean_object* v_l_4157_; lean_object* v_r_4158_; lean_object* v_size_4159_; lean_object* v_k_4160_; lean_object* v_v_4161_; lean_object* v_l_4162_; lean_object* v_r_4163_; lean_object* v___x_4164_; 
lean_inc_ref(v_r_4150_);
lean_dec(v_h__4_4147_);
v_size_4151_ = lean_ctor_get(v_r_4141_, 0);
lean_inc(v_size_4151_);
v_k_4152_ = lean_ctor_get(v_r_4141_, 1);
lean_inc(v_k_4152_);
v_v_4153_ = lean_ctor_get(v_r_4141_, 2);
lean_inc(v_v_4153_);
lean_dec_ref(v_r_4141_);
v_size_4154_ = lean_ctor_get(v_l_4149_, 0);
lean_inc(v_size_4154_);
v_k_4155_ = lean_ctor_get(v_l_4149_, 1);
lean_inc(v_k_4155_);
v_v_4156_ = lean_ctor_get(v_l_4149_, 2);
lean_inc(v_v_4156_);
v_l_4157_ = lean_ctor_get(v_l_4149_, 3);
lean_inc(v_l_4157_);
v_r_4158_ = lean_ctor_get(v_l_4149_, 4);
lean_inc(v_r_4158_);
lean_dec_ref(v_l_4149_);
v_size_4159_ = lean_ctor_get(v_r_4150_, 0);
lean_inc(v_size_4159_);
v_k_4160_ = lean_ctor_get(v_r_4150_, 1);
lean_inc(v_k_4160_);
v_v_4161_ = lean_ctor_get(v_r_4150_, 2);
lean_inc(v_v_4161_);
v_l_4162_ = lean_ctor_get(v_r_4150_, 3);
lean_inc(v_l_4162_);
v_r_4163_ = lean_ctor_get(v_r_4150_, 4);
lean_inc(v_r_4163_);
lean_dec_ref(v_r_4150_);
v___x_4164_ = lean_apply_15(v_h__5_4148_, v_size_4151_, v_k_4152_, v_v_4153_, v_size_4154_, v_k_4155_, v_v_4156_, v_l_4157_, v_r_4158_, v_size_4159_, v_k_4160_, v_v_4161_, v_l_4162_, v_r_4163_, lean_box(0), lean_box(0));
return v___x_4164_;
}
else
{
lean_object* v_size_4165_; lean_object* v_k_4166_; lean_object* v_v_4167_; lean_object* v_size_4168_; lean_object* v_k_4169_; lean_object* v_v_4170_; lean_object* v_l_4171_; lean_object* v_r_4172_; lean_object* v___x_4173_; 
lean_dec(v_h__5_4148_);
v_size_4165_ = lean_ctor_get(v_r_4141_, 0);
lean_inc(v_size_4165_);
v_k_4166_ = lean_ctor_get(v_r_4141_, 1);
lean_inc(v_k_4166_);
v_v_4167_ = lean_ctor_get(v_r_4141_, 2);
lean_inc(v_v_4167_);
lean_dec_ref(v_r_4141_);
v_size_4168_ = lean_ctor_get(v_l_4149_, 0);
lean_inc(v_size_4168_);
v_k_4169_ = lean_ctor_get(v_l_4149_, 1);
lean_inc(v_k_4169_);
v_v_4170_ = lean_ctor_get(v_l_4149_, 2);
lean_inc(v_v_4170_);
v_l_4171_ = lean_ctor_get(v_l_4149_, 3);
lean_inc(v_l_4171_);
v_r_4172_ = lean_ctor_get(v_l_4149_, 4);
lean_inc(v_r_4172_);
lean_dec_ref(v_l_4149_);
v___x_4173_ = lean_apply_10(v_h__4_4147_, v_size_4165_, v_k_4166_, v_v_4167_, v_size_4168_, v_k_4169_, v_v_4170_, v_l_4171_, v_r_4172_, lean_box(0), lean_box(0));
return v___x_4173_;
}
}
else
{
lean_object* v_r_4174_; 
lean_dec(v_h__5_4148_);
lean_dec(v_h__4_4147_);
v_r_4174_ = lean_ctor_get(v_r_4141_, 4);
if (lean_obj_tag(v_r_4174_) == 0)
{
lean_object* v_size_4175_; lean_object* v_k_4176_; lean_object* v_v_4177_; lean_object* v_size_4178_; lean_object* v_k_4179_; lean_object* v_v_4180_; lean_object* v_l_4181_; lean_object* v_r_4182_; lean_object* v___x_4183_; 
lean_inc_ref(v_r_4174_);
lean_dec(v_h__2_4145_);
v_size_4175_ = lean_ctor_get(v_r_4141_, 0);
lean_inc(v_size_4175_);
v_k_4176_ = lean_ctor_get(v_r_4141_, 1);
lean_inc(v_k_4176_);
v_v_4177_ = lean_ctor_get(v_r_4141_, 2);
lean_inc(v_v_4177_);
lean_dec_ref(v_r_4141_);
v_size_4178_ = lean_ctor_get(v_r_4174_, 0);
lean_inc(v_size_4178_);
v_k_4179_ = lean_ctor_get(v_r_4174_, 1);
lean_inc(v_k_4179_);
v_v_4180_ = lean_ctor_get(v_r_4174_, 2);
lean_inc(v_v_4180_);
v_l_4181_ = lean_ctor_get(v_r_4174_, 3);
lean_inc(v_l_4181_);
v_r_4182_ = lean_ctor_get(v_r_4174_, 4);
lean_inc(v_r_4182_);
lean_dec_ref(v_r_4174_);
v___x_4183_ = lean_apply_10(v_h__3_4146_, v_size_4175_, v_k_4176_, v_v_4177_, v_size_4178_, v_k_4179_, v_v_4180_, v_l_4181_, v_r_4182_, lean_box(0), lean_box(0));
return v___x_4183_;
}
else
{
lean_object* v_size_4184_; lean_object* v_k_4185_; lean_object* v_v_4186_; lean_object* v___x_4187_; 
lean_dec(v_h__3_4146_);
v_size_4184_ = lean_ctor_get(v_r_4141_, 0);
lean_inc(v_size_4184_);
v_k_4185_ = lean_ctor_get(v_r_4141_, 1);
lean_inc(v_k_4185_);
v_v_4186_ = lean_ctor_get(v_r_4141_, 2);
lean_inc(v_v_4186_);
lean_dec_ref(v_r_4141_);
v___x_4187_ = lean_apply_5(v_h__2_4145_, v_size_4184_, v_k_4185_, v_v_4186_, lean_box(0), lean_box(0));
return v___x_4187_;
}
}
}
else
{
lean_object* v___x_4188_; 
lean_dec(v_h__5_4148_);
lean_dec(v_h__4_4147_);
lean_dec(v_h__3_4146_);
lean_dec(v_h__2_4145_);
v___x_4188_ = lean_apply_2(v_h__1_4144_, lean_box(0), lean_box(0));
return v___x_4188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___redArg(lean_object* v_l_4189_, lean_object* v_h__1_4190_, lean_object* v_h__2_4191_){
_start:
{
if (lean_obj_tag(v_l_4189_) == 0)
{
lean_object* v_size_4192_; lean_object* v_k_4193_; lean_object* v_v_4194_; lean_object* v_l_4195_; lean_object* v_r_4196_; lean_object* v___x_4197_; 
lean_dec(v_h__1_4190_);
v_size_4192_ = lean_ctor_get(v_l_4189_, 0);
lean_inc(v_size_4192_);
v_k_4193_ = lean_ctor_get(v_l_4189_, 1);
lean_inc(v_k_4193_);
v_v_4194_ = lean_ctor_get(v_l_4189_, 2);
lean_inc(v_v_4194_);
v_l_4195_ = lean_ctor_get(v_l_4189_, 3);
lean_inc(v_l_4195_);
v_r_4196_ = lean_ctor_get(v_l_4189_, 4);
lean_inc(v_r_4196_);
lean_dec_ref(v_l_4189_);
v___x_4197_ = lean_apply_7(v_h__2_4191_, v_size_4192_, v_k_4193_, v_v_4194_, v_l_4195_, v_r_4196_, lean_box(0), lean_box(0));
return v___x_4197_;
}
else
{
lean_object* v___x_4198_; 
lean_dec(v_h__2_4191_);
v___x_4198_ = lean_apply_2(v_h__1_4190_, lean_box(0), lean_box(0));
return v___x_4198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter(lean_object* v_00_u03b1_4199_, lean_object* v_00_u03b2_4200_, lean_object* v_rs_4201_, lean_object* v_k_4202_, lean_object* v_v_4203_, lean_object* v_l_4204_, lean_object* v_r_4205_, lean_object* v_motive_4206_, lean_object* v_l_4207_, lean_object* v_hlb_4208_, lean_object* v_hlr_4209_, lean_object* v_h__1_4210_, lean_object* v_h__2_4211_){
_start:
{
if (lean_obj_tag(v_l_4207_) == 0)
{
lean_object* v_size_4212_; lean_object* v_k_4213_; lean_object* v_v_4214_; lean_object* v_l_4215_; lean_object* v_r_4216_; lean_object* v___x_4217_; 
lean_dec(v_h__1_4210_);
v_size_4212_ = lean_ctor_get(v_l_4207_, 0);
lean_inc(v_size_4212_);
v_k_4213_ = lean_ctor_get(v_l_4207_, 1);
lean_inc(v_k_4213_);
v_v_4214_ = lean_ctor_get(v_l_4207_, 2);
lean_inc(v_v_4214_);
v_l_4215_ = lean_ctor_get(v_l_4207_, 3);
lean_inc(v_l_4215_);
v_r_4216_ = lean_ctor_get(v_l_4207_, 4);
lean_inc(v_r_4216_);
lean_dec_ref(v_l_4207_);
v___x_4217_ = lean_apply_7(v_h__2_4211_, v_size_4212_, v_k_4213_, v_v_4214_, v_l_4215_, v_r_4216_, lean_box(0), lean_box(0));
return v___x_4217_;
}
else
{
lean_object* v___x_4218_; 
lean_dec(v_h__2_4211_);
v___x_4218_ = lean_apply_2(v_h__1_4210_, lean_box(0), lean_box(0));
return v___x_4218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter___boxed(lean_object* v_00_u03b1_4219_, lean_object* v_00_u03b2_4220_, lean_object* v_rs_4221_, lean_object* v_k_4222_, lean_object* v_v_4223_, lean_object* v_l_4224_, lean_object* v_r_4225_, lean_object* v_motive_4226_, lean_object* v_l_4227_, lean_object* v_hlb_4228_, lean_object* v_hlr_4229_, lean_object* v_h__1_4230_, lean_object* v_h__2_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceLErase_match__5_splitter(v_00_u03b1_4219_, v_00_u03b2_4220_, v_rs_4221_, v_k_4222_, v_v_4223_, v_l_4224_, v_r_4225_, v_motive_4226_, v_l_4227_, v_hlb_4228_, v_hlr_4229_, v_h__1_4230_, v_h__2_4231_);
lean_dec(v_r_4225_);
lean_dec(v_l_4224_);
lean_dec(v_v_4223_);
lean_dec(v_k_4222_);
lean_dec(v_rs_4221_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter___redArg(lean_object* v_r_4233_, lean_object* v_h__1_4234_, lean_object* v_h__2_4235_, lean_object* v_h__3_4236_, lean_object* v_h__4_4237_, lean_object* v_h__5_4238_){
_start:
{
if (lean_obj_tag(v_r_4233_) == 0)
{
lean_object* v_l_4239_; 
lean_dec(v_h__1_4234_);
v_l_4239_ = lean_ctor_get(v_r_4233_, 3);
if (lean_obj_tag(v_l_4239_) == 0)
{
lean_object* v_r_4240_; 
lean_inc_ref(v_l_4239_);
lean_dec(v_h__3_4236_);
lean_dec(v_h__2_4235_);
v_r_4240_ = lean_ctor_get(v_r_4233_, 4);
if (lean_obj_tag(v_r_4240_) == 0)
{
lean_object* v_size_4241_; lean_object* v_k_4242_; lean_object* v_v_4243_; lean_object* v_size_4244_; lean_object* v_k_4245_; lean_object* v_v_4246_; lean_object* v_l_4247_; lean_object* v_r_4248_; lean_object* v_size_4249_; lean_object* v_k_4250_; lean_object* v_v_4251_; lean_object* v_l_4252_; lean_object* v_r_4253_; lean_object* v___x_4254_; 
lean_inc_ref(v_r_4240_);
lean_dec(v_h__4_4237_);
v_size_4241_ = lean_ctor_get(v_r_4233_, 0);
lean_inc(v_size_4241_);
v_k_4242_ = lean_ctor_get(v_r_4233_, 1);
lean_inc(v_k_4242_);
v_v_4243_ = lean_ctor_get(v_r_4233_, 2);
lean_inc(v_v_4243_);
lean_dec_ref(v_r_4233_);
v_size_4244_ = lean_ctor_get(v_l_4239_, 0);
lean_inc(v_size_4244_);
v_k_4245_ = lean_ctor_get(v_l_4239_, 1);
lean_inc(v_k_4245_);
v_v_4246_ = lean_ctor_get(v_l_4239_, 2);
lean_inc(v_v_4246_);
v_l_4247_ = lean_ctor_get(v_l_4239_, 3);
lean_inc(v_l_4247_);
v_r_4248_ = lean_ctor_get(v_l_4239_, 4);
lean_inc(v_r_4248_);
lean_dec_ref(v_l_4239_);
v_size_4249_ = lean_ctor_get(v_r_4240_, 0);
lean_inc(v_size_4249_);
v_k_4250_ = lean_ctor_get(v_r_4240_, 1);
lean_inc(v_k_4250_);
v_v_4251_ = lean_ctor_get(v_r_4240_, 2);
lean_inc(v_v_4251_);
v_l_4252_ = lean_ctor_get(v_r_4240_, 3);
lean_inc(v_l_4252_);
v_r_4253_ = lean_ctor_get(v_r_4240_, 4);
lean_inc(v_r_4253_);
lean_dec_ref(v_r_4240_);
v___x_4254_ = lean_apply_13(v_h__5_4238_, v_size_4241_, v_k_4242_, v_v_4243_, v_size_4244_, v_k_4245_, v_v_4246_, v_l_4247_, v_r_4248_, v_size_4249_, v_k_4250_, v_v_4251_, v_l_4252_, v_r_4253_);
return v___x_4254_;
}
else
{
lean_object* v_size_4255_; lean_object* v_k_4256_; lean_object* v_v_4257_; lean_object* v_size_4258_; lean_object* v_k_4259_; lean_object* v_v_4260_; lean_object* v_l_4261_; lean_object* v_r_4262_; lean_object* v___x_4263_; 
lean_dec(v_h__5_4238_);
v_size_4255_ = lean_ctor_get(v_r_4233_, 0);
lean_inc(v_size_4255_);
v_k_4256_ = lean_ctor_get(v_r_4233_, 1);
lean_inc(v_k_4256_);
v_v_4257_ = lean_ctor_get(v_r_4233_, 2);
lean_inc(v_v_4257_);
lean_dec_ref(v_r_4233_);
v_size_4258_ = lean_ctor_get(v_l_4239_, 0);
lean_inc(v_size_4258_);
v_k_4259_ = lean_ctor_get(v_l_4239_, 1);
lean_inc(v_k_4259_);
v_v_4260_ = lean_ctor_get(v_l_4239_, 2);
lean_inc(v_v_4260_);
v_l_4261_ = lean_ctor_get(v_l_4239_, 3);
lean_inc(v_l_4261_);
v_r_4262_ = lean_ctor_get(v_l_4239_, 4);
lean_inc(v_r_4262_);
lean_dec_ref(v_l_4239_);
v___x_4263_ = lean_apply_8(v_h__4_4237_, v_size_4255_, v_k_4256_, v_v_4257_, v_size_4258_, v_k_4259_, v_v_4260_, v_l_4261_, v_r_4262_);
return v___x_4263_;
}
}
else
{
lean_object* v_r_4264_; 
lean_dec(v_h__5_4238_);
lean_dec(v_h__4_4237_);
v_r_4264_ = lean_ctor_get(v_r_4233_, 4);
if (lean_obj_tag(v_r_4264_) == 0)
{
lean_object* v_size_4265_; lean_object* v_k_4266_; lean_object* v_v_4267_; lean_object* v_size_4268_; lean_object* v_k_4269_; lean_object* v_v_4270_; lean_object* v_l_4271_; lean_object* v_r_4272_; lean_object* v___x_4273_; 
lean_inc_ref(v_r_4264_);
lean_dec(v_h__2_4235_);
v_size_4265_ = lean_ctor_get(v_r_4233_, 0);
lean_inc(v_size_4265_);
v_k_4266_ = lean_ctor_get(v_r_4233_, 1);
lean_inc(v_k_4266_);
v_v_4267_ = lean_ctor_get(v_r_4233_, 2);
lean_inc(v_v_4267_);
lean_dec_ref(v_r_4233_);
v_size_4268_ = lean_ctor_get(v_r_4264_, 0);
lean_inc(v_size_4268_);
v_k_4269_ = lean_ctor_get(v_r_4264_, 1);
lean_inc(v_k_4269_);
v_v_4270_ = lean_ctor_get(v_r_4264_, 2);
lean_inc(v_v_4270_);
v_l_4271_ = lean_ctor_get(v_r_4264_, 3);
lean_inc(v_l_4271_);
v_r_4272_ = lean_ctor_get(v_r_4264_, 4);
lean_inc(v_r_4272_);
lean_dec_ref(v_r_4264_);
v___x_4273_ = lean_apply_8(v_h__3_4236_, v_size_4265_, v_k_4266_, v_v_4267_, v_size_4268_, v_k_4269_, v_v_4270_, v_l_4271_, v_r_4272_);
return v___x_4273_;
}
else
{
lean_object* v_size_4274_; lean_object* v_k_4275_; lean_object* v_v_4276_; lean_object* v___x_4277_; 
lean_dec(v_h__3_4236_);
v_size_4274_ = lean_ctor_get(v_r_4233_, 0);
lean_inc(v_size_4274_);
v_k_4275_ = lean_ctor_get(v_r_4233_, 1);
lean_inc(v_k_4275_);
v_v_4276_ = lean_ctor_get(v_r_4233_, 2);
lean_inc(v_v_4276_);
lean_dec_ref(v_r_4233_);
v___x_4277_ = lean_apply_3(v_h__2_4235_, v_size_4274_, v_k_4275_, v_v_4276_);
return v___x_4277_;
}
}
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_dec(v_h__5_4238_);
lean_dec(v_h__4_4237_);
lean_dec(v_h__3_4236_);
lean_dec(v_h__2_4235_);
v___x_4278_ = lean_box(0);
v___x_4279_ = lean_apply_1(v_h__1_4234_, v___x_4278_);
return v___x_4279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balanceR_x21_match__1_splitter(lean_object* v_00_u03b1_4280_, lean_object* v_00_u03b2_4281_, lean_object* v_motive_4282_, lean_object* v_r_4283_, lean_object* v_h__1_4284_, lean_object* v_h__2_4285_, lean_object* v_h__3_4286_, lean_object* v_h__4_4287_, lean_object* v_h__5_4288_){
_start:
{
if (lean_obj_tag(v_r_4283_) == 0)
{
lean_object* v_l_4289_; 
lean_dec(v_h__1_4284_);
v_l_4289_ = lean_ctor_get(v_r_4283_, 3);
if (lean_obj_tag(v_l_4289_) == 0)
{
lean_object* v_r_4290_; 
lean_inc_ref(v_l_4289_);
lean_dec(v_h__3_4286_);
lean_dec(v_h__2_4285_);
v_r_4290_ = lean_ctor_get(v_r_4283_, 4);
if (lean_obj_tag(v_r_4290_) == 0)
{
lean_object* v_size_4291_; lean_object* v_k_4292_; lean_object* v_v_4293_; lean_object* v_size_4294_; lean_object* v_k_4295_; lean_object* v_v_4296_; lean_object* v_l_4297_; lean_object* v_r_4298_; lean_object* v_size_4299_; lean_object* v_k_4300_; lean_object* v_v_4301_; lean_object* v_l_4302_; lean_object* v_r_4303_; lean_object* v___x_4304_; 
lean_inc_ref(v_r_4290_);
lean_dec(v_h__4_4287_);
v_size_4291_ = lean_ctor_get(v_r_4283_, 0);
lean_inc(v_size_4291_);
v_k_4292_ = lean_ctor_get(v_r_4283_, 1);
lean_inc(v_k_4292_);
v_v_4293_ = lean_ctor_get(v_r_4283_, 2);
lean_inc(v_v_4293_);
lean_dec_ref(v_r_4283_);
v_size_4294_ = lean_ctor_get(v_l_4289_, 0);
lean_inc(v_size_4294_);
v_k_4295_ = lean_ctor_get(v_l_4289_, 1);
lean_inc(v_k_4295_);
v_v_4296_ = lean_ctor_get(v_l_4289_, 2);
lean_inc(v_v_4296_);
v_l_4297_ = lean_ctor_get(v_l_4289_, 3);
lean_inc(v_l_4297_);
v_r_4298_ = lean_ctor_get(v_l_4289_, 4);
lean_inc(v_r_4298_);
lean_dec_ref(v_l_4289_);
v_size_4299_ = lean_ctor_get(v_r_4290_, 0);
lean_inc(v_size_4299_);
v_k_4300_ = lean_ctor_get(v_r_4290_, 1);
lean_inc(v_k_4300_);
v_v_4301_ = lean_ctor_get(v_r_4290_, 2);
lean_inc(v_v_4301_);
v_l_4302_ = lean_ctor_get(v_r_4290_, 3);
lean_inc(v_l_4302_);
v_r_4303_ = lean_ctor_get(v_r_4290_, 4);
lean_inc(v_r_4303_);
lean_dec_ref(v_r_4290_);
v___x_4304_ = lean_apply_13(v_h__5_4288_, v_size_4291_, v_k_4292_, v_v_4293_, v_size_4294_, v_k_4295_, v_v_4296_, v_l_4297_, v_r_4298_, v_size_4299_, v_k_4300_, v_v_4301_, v_l_4302_, v_r_4303_);
return v___x_4304_;
}
else
{
lean_object* v_size_4305_; lean_object* v_k_4306_; lean_object* v_v_4307_; lean_object* v_size_4308_; lean_object* v_k_4309_; lean_object* v_v_4310_; lean_object* v_l_4311_; lean_object* v_r_4312_; lean_object* v___x_4313_; 
lean_dec(v_h__5_4288_);
v_size_4305_ = lean_ctor_get(v_r_4283_, 0);
lean_inc(v_size_4305_);
v_k_4306_ = lean_ctor_get(v_r_4283_, 1);
lean_inc(v_k_4306_);
v_v_4307_ = lean_ctor_get(v_r_4283_, 2);
lean_inc(v_v_4307_);
lean_dec_ref(v_r_4283_);
v_size_4308_ = lean_ctor_get(v_l_4289_, 0);
lean_inc(v_size_4308_);
v_k_4309_ = lean_ctor_get(v_l_4289_, 1);
lean_inc(v_k_4309_);
v_v_4310_ = lean_ctor_get(v_l_4289_, 2);
lean_inc(v_v_4310_);
v_l_4311_ = lean_ctor_get(v_l_4289_, 3);
lean_inc(v_l_4311_);
v_r_4312_ = lean_ctor_get(v_l_4289_, 4);
lean_inc(v_r_4312_);
lean_dec_ref(v_l_4289_);
v___x_4313_ = lean_apply_8(v_h__4_4287_, v_size_4305_, v_k_4306_, v_v_4307_, v_size_4308_, v_k_4309_, v_v_4310_, v_l_4311_, v_r_4312_);
return v___x_4313_;
}
}
else
{
lean_object* v_r_4314_; 
lean_dec(v_h__5_4288_);
lean_dec(v_h__4_4287_);
v_r_4314_ = lean_ctor_get(v_r_4283_, 4);
if (lean_obj_tag(v_r_4314_) == 0)
{
lean_object* v_size_4315_; lean_object* v_k_4316_; lean_object* v_v_4317_; lean_object* v_size_4318_; lean_object* v_k_4319_; lean_object* v_v_4320_; lean_object* v_l_4321_; lean_object* v_r_4322_; lean_object* v___x_4323_; 
lean_inc_ref(v_r_4314_);
lean_dec(v_h__2_4285_);
v_size_4315_ = lean_ctor_get(v_r_4283_, 0);
lean_inc(v_size_4315_);
v_k_4316_ = lean_ctor_get(v_r_4283_, 1);
lean_inc(v_k_4316_);
v_v_4317_ = lean_ctor_get(v_r_4283_, 2);
lean_inc(v_v_4317_);
lean_dec_ref(v_r_4283_);
v_size_4318_ = lean_ctor_get(v_r_4314_, 0);
lean_inc(v_size_4318_);
v_k_4319_ = lean_ctor_get(v_r_4314_, 1);
lean_inc(v_k_4319_);
v_v_4320_ = lean_ctor_get(v_r_4314_, 2);
lean_inc(v_v_4320_);
v_l_4321_ = lean_ctor_get(v_r_4314_, 3);
lean_inc(v_l_4321_);
v_r_4322_ = lean_ctor_get(v_r_4314_, 4);
lean_inc(v_r_4322_);
lean_dec_ref(v_r_4314_);
v___x_4323_ = lean_apply_8(v_h__3_4286_, v_size_4315_, v_k_4316_, v_v_4317_, v_size_4318_, v_k_4319_, v_v_4320_, v_l_4321_, v_r_4322_);
return v___x_4323_;
}
else
{
lean_object* v_size_4324_; lean_object* v_k_4325_; lean_object* v_v_4326_; lean_object* v___x_4327_; 
lean_dec(v_h__3_4286_);
v_size_4324_ = lean_ctor_get(v_r_4283_, 0);
lean_inc(v_size_4324_);
v_k_4325_ = lean_ctor_get(v_r_4283_, 1);
lean_inc(v_k_4325_);
v_v_4326_ = lean_ctor_get(v_r_4283_, 2);
lean_inc(v_v_4326_);
lean_dec_ref(v_r_4283_);
v___x_4327_ = lean_apply_3(v_h__2_4285_, v_size_4324_, v_k_4325_, v_v_4326_);
return v___x_4327_;
}
}
}
else
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
lean_dec(v_h__5_4288_);
lean_dec(v_h__4_4287_);
lean_dec(v_h__3_4286_);
lean_dec(v_h__2_4285_);
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_apply_1(v_h__1_4284_, v___x_4328_);
return v___x_4329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___redArg(lean_object* v_r_4330_, lean_object* v_h__1_4331_, lean_object* v_h__2_4332_){
_start:
{
if (lean_obj_tag(v_r_4330_) == 0)
{
lean_object* v_size_4333_; lean_object* v_k_4334_; lean_object* v_v_4335_; lean_object* v_l_4336_; lean_object* v_r_4337_; lean_object* v___x_4338_; 
lean_dec(v_h__1_4331_);
v_size_4333_ = lean_ctor_get(v_r_4330_, 0);
lean_inc(v_size_4333_);
v_k_4334_ = lean_ctor_get(v_r_4330_, 1);
lean_inc(v_k_4334_);
v_v_4335_ = lean_ctor_get(v_r_4330_, 2);
lean_inc(v_v_4335_);
v_l_4336_ = lean_ctor_get(v_r_4330_, 3);
lean_inc(v_l_4336_);
v_r_4337_ = lean_ctor_get(v_r_4330_, 4);
lean_inc(v_r_4337_);
lean_dec_ref(v_r_4330_);
v___x_4338_ = lean_apply_6(v_h__2_4332_, v_size_4333_, v_k_4334_, v_v_4335_, v_l_4336_, v_r_4337_, lean_box(0));
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; 
lean_dec(v_h__2_4332_);
v___x_4339_ = lean_apply_1(v_h__1_4331_, lean_box(0));
return v___x_4339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(lean_object* v_00_u03b1_4340_, lean_object* v_00_u03b2_4341_, lean_object* v_l_4342_, lean_object* v_motive_4343_, lean_object* v_r_4344_, lean_object* v_h_4345_, lean_object* v_h__1_4346_, lean_object* v_h__2_4347_){
_start:
{
if (lean_obj_tag(v_r_4344_) == 0)
{
lean_object* v_size_4348_; lean_object* v_k_4349_; lean_object* v_v_4350_; lean_object* v_l_4351_; lean_object* v_r_4352_; lean_object* v___x_4353_; 
lean_dec(v_h__1_4346_);
v_size_4348_ = lean_ctor_get(v_r_4344_, 0);
lean_inc(v_size_4348_);
v_k_4349_ = lean_ctor_get(v_r_4344_, 1);
lean_inc(v_k_4349_);
v_v_4350_ = lean_ctor_get(v_r_4344_, 2);
lean_inc(v_v_4350_);
v_l_4351_ = lean_ctor_get(v_r_4344_, 3);
lean_inc(v_l_4351_);
v_r_4352_ = lean_ctor_get(v_r_4344_, 4);
lean_inc(v_r_4352_);
lean_dec_ref(v_r_4344_);
v___x_4353_ = lean_apply_6(v_h__2_4347_, v_size_4348_, v_k_4349_, v_v_4350_, v_l_4351_, v_r_4352_, lean_box(0));
return v___x_4353_;
}
else
{
lean_object* v___x_4354_; 
lean_dec(v_h__2_4347_);
v___x_4354_ = lean_apply_1(v_h__1_4346_, lean_box(0));
return v___x_4354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_4355_, lean_object* v_00_u03b2_4356_, lean_object* v_l_4357_, lean_object* v_motive_4358_, lean_object* v_r_4359_, lean_object* v_h_4360_, lean_object* v_h__1_4361_, lean_object* v_h__2_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__1_splitter(v_00_u03b1_4355_, v_00_u03b2_4356_, v_l_4357_, v_motive_4358_, v_r_4359_, v_h_4360_, v_h__1_4361_, v_h__2_4362_);
lean_dec(v_l_4357_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___redArg(lean_object* v_l_4364_, lean_object* v_h__1_4365_, lean_object* v_h__2_4366_){
_start:
{
if (lean_obj_tag(v_l_4364_) == 0)
{
lean_object* v_size_4367_; lean_object* v_k_4368_; lean_object* v_v_4369_; lean_object* v_l_4370_; lean_object* v_r_4371_; lean_object* v___x_4372_; 
lean_dec(v_h__1_4365_);
v_size_4367_ = lean_ctor_get(v_l_4364_, 0);
lean_inc(v_size_4367_);
v_k_4368_ = lean_ctor_get(v_l_4364_, 1);
lean_inc(v_k_4368_);
v_v_4369_ = lean_ctor_get(v_l_4364_, 2);
lean_inc(v_v_4369_);
v_l_4370_ = lean_ctor_get(v_l_4364_, 3);
lean_inc(v_l_4370_);
v_r_4371_ = lean_ctor_get(v_l_4364_, 4);
lean_inc(v_r_4371_);
lean_dec_ref(v_l_4364_);
v___x_4372_ = lean_apply_7(v_h__2_4366_, v_size_4367_, v_k_4368_, v_v_4369_, v_l_4370_, v_r_4371_, lean_box(0), lean_box(0));
return v___x_4372_;
}
else
{
lean_object* v___x_4373_; 
lean_dec(v_h__2_4366_);
v___x_4373_ = lean_apply_2(v_h__1_4365_, lean_box(0), lean_box(0));
return v___x_4373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(lean_object* v_00_u03b1_4374_, lean_object* v_00_u03b2_4375_, lean_object* v_r_4376_, lean_object* v_motive_4377_, lean_object* v_l_4378_, lean_object* v_h_4379_, lean_object* v_h_4380_, lean_object* v_h__1_4381_, lean_object* v_h__2_4382_){
_start:
{
if (lean_obj_tag(v_l_4378_) == 0)
{
lean_object* v_size_4383_; lean_object* v_k_4384_; lean_object* v_v_4385_; lean_object* v_l_4386_; lean_object* v_r_4387_; lean_object* v___x_4388_; 
lean_dec(v_h__1_4381_);
v_size_4383_ = lean_ctor_get(v_l_4378_, 0);
lean_inc(v_size_4383_);
v_k_4384_ = lean_ctor_get(v_l_4378_, 1);
lean_inc(v_k_4384_);
v_v_4385_ = lean_ctor_get(v_l_4378_, 2);
lean_inc(v_v_4385_);
v_l_4386_ = lean_ctor_get(v_l_4378_, 3);
lean_inc(v_l_4386_);
v_r_4387_ = lean_ctor_get(v_l_4378_, 4);
lean_inc(v_r_4387_);
lean_dec_ref(v_l_4378_);
v___x_4388_ = lean_apply_7(v_h__2_4382_, v_size_4383_, v_k_4384_, v_v_4385_, v_l_4386_, v_r_4387_, lean_box(0), lean_box(0));
return v___x_4388_;
}
else
{
lean_object* v___x_4389_; 
lean_dec(v_h__2_4382_);
v___x_4389_ = lean_apply_2(v_h__1_4381_, lean_box(0), lean_box(0));
return v___x_4389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter___boxed(lean_object* v_00_u03b1_4390_, lean_object* v_00_u03b2_4391_, lean_object* v_r_4392_, lean_object* v_motive_4393_, lean_object* v_l_4394_, lean_object* v_h_4395_, lean_object* v_h_4396_, lean_object* v_h__1_4397_, lean_object* v_h__2_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Std_Data_DTreeMap_Internal_Balancing_0__Std_DTreeMap_Internal_Impl_balance_u2098_match__3_splitter(v_00_u03b1_4390_, v_00_u03b2_4391_, v_r_4392_, v_motive_4393_, v_l_4394_, v_h_4395_, v_h_4396_, v_h__1_4397_, v_h__2_4398_);
lean_dec(v_r_4392_);
return v_res_4399_;
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
