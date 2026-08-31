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
v___x_481_ = lean_nat_add(v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec(v___y_479_);
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
lean_ctor_set(v___x_460_, 3, v___y_478_);
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
lean_ctor_set(v_reuseFailAlloc_486_, 3, v___y_478_);
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
v___y_478_ = v___x_492_;
v___y_479_ = v___x_493_;
v___y_480_ = v_size_494_;
goto v___jp_477_;
}
else
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___y_478_ = v___x_492_;
v___y_479_ = v___x_493_;
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
v___x_626_ = lean_nat_add(v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec(v___y_624_);
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
lean_ctor_set(v___x_605_, 3, v___y_623_);
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
lean_ctor_set(v_reuseFailAlloc_631_, 3, v___y_623_);
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
v___y_623_ = v___x_637_;
v___y_624_ = v___x_638_;
v___y_625_ = v_size_639_;
goto v___jp_622_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___y_623_ = v___x_637_;
v___y_624_ = v___x_638_;
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
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1172_; 
lean_inc(v_l_1093_);
lean_inc(v_v_1092_);
lean_inc(v_k_1091_);
lean_inc(v_size_1090_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; 
v_unused_1173_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_l_1087_, 2);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_l_1087_, 1);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_l_1087_, 0);
lean_dec(v_unused_1177_);
v___x_1103_ = v_l_1087_;
v_isShared_1104_ = v_isSharedCheck_1172_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_l_1087_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1172_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_box(1);
if (lean_obj_tag(v_l_1093_) == 0)
{
if (lean_obj_tag(v_r_1094_) == 0)
{
lean_object* v_size_1106_; lean_object* v_size_1107_; lean_object* v_k_1108_; lean_object* v_v_1109_; lean_object* v_l_1110_; lean_object* v_r_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_size_1106_ = lean_ctor_get(v_l_1093_, 0);
v_size_1107_ = lean_ctor_get(v_r_1094_, 0);
v_k_1108_ = lean_ctor_get(v_r_1094_, 1);
v_v_1109_ = lean_ctor_get(v_r_1094_, 2);
v_l_1110_ = lean_ctor_get(v_r_1094_, 3);
v_r_1111_ = lean_ctor_get(v_r_1094_, 4);
v___x_1112_ = lean_unsigned_to_nat(2u);
v___x_1113_ = lean_nat_mul(v___x_1112_, v_size_1106_);
v___x_1114_ = lean_nat_dec_lt(v_size_1107_, v___x_1113_);
lean_dec(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1142_; 
lean_inc(v_r_1111_);
lean_inc(v_l_1110_);
lean_inc(v_v_1109_);
lean_inc(v_k_1108_);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_r_1094_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1143_ = lean_ctor_get(v_r_1094_, 4);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_r_1094_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_r_1094_, 2);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_r_1094_, 1);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_r_1094_, 0);
lean_dec(v_unused_1147_);
v___x_1116_ = v_r_1094_;
v_isShared_1117_ = v_isSharedCheck_1142_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_r_1094_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1142_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___x_1132_; lean_object* v___y_1134_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v___x_1118_, v_size_1090_);
lean_dec(v_size_1090_);
v___x_1120_ = lean_nat_add(v___x_1119_, v_size_1089_);
lean_dec(v___x_1119_);
v___x_1132_ = lean_nat_add(v___x_1118_, v_size_1106_);
if (lean_obj_tag(v_l_1110_) == 0)
{
lean_object* v_size_1140_; 
v_size_1140_ = lean_ctor_get(v_l_1110_, 0);
lean_inc(v_size_1140_);
v___y_1134_ = v_size_1140_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___y_1134_ = v___x_1141_;
goto v___jp_1133_;
}
v___jp_1121_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_nat_add(v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec(v___y_1123_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v_r_1088_);
lean_ctor_set(v___x_1116_, 3, v_r_1111_);
lean_ctor_set(v___x_1116_, 2, v_v_1086_);
lean_ctor_set(v___x_1116_, 1, v_k_1085_);
lean_ctor_set(v___x_1116_, 0, v___x_1125_);
v___x_1127_ = v___x_1116_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_r_1111_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_r_1088_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v___x_1127_);
lean_ctor_set(v___x_1103_, 3, v___y_1122_);
lean_ctor_set(v___x_1103_, 2, v_v_1109_);
lean_ctor_set(v___x_1103_, 1, v_k_1108_);
lean_ctor_set(v___x_1103_, 0, v___x_1120_);
v___x_1129_ = v___x_1103_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_1108_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_1109_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v___y_1122_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
v___jp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_nat_add(v___x_1132_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_k_1091_);
lean_ctor_set(v___x_1136_, 2, v_v_1092_);
lean_ctor_set(v___x_1136_, 3, v_l_1093_);
lean_ctor_set(v___x_1136_, 4, v_l_1110_);
v___x_1137_ = lean_nat_add(v___x_1118_, v_size_1089_);
if (lean_obj_tag(v_r_1111_) == 0)
{
lean_object* v_size_1138_; 
v_size_1138_ = lean_ctor_get(v_r_1111_, 0);
lean_inc(v_size_1138_);
v___y_1122_ = v___x_1136_;
v___y_1123_ = v___x_1137_;
v___y_1124_ = v_size_1138_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_unsigned_to_nat(0u);
v___y_1122_ = v___x_1136_;
v___y_1123_ = v___x_1137_;
v___y_1124_ = v___x_1139_;
goto v___jp_1121_;
}
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v___x_1148_, v_size_1090_);
lean_dec(v_size_1090_);
v___x_1150_ = lean_nat_add(v___x_1149_, v_size_1089_);
lean_dec(v___x_1149_);
v___x_1151_ = lean_nat_add(v___x_1148_, v_size_1089_);
v___x_1152_ = lean_nat_add(v___x_1151_, v_size_1107_);
lean_dec(v___x_1151_);
lean_inc_ref(v_r_1088_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_r_1088_);
lean_ctor_set(v___x_1103_, 3, v_r_1094_);
lean_ctor_set(v___x_1103_, 2, v_v_1086_);
lean_ctor_set(v___x_1103_, 1, v_k_1085_);
lean_ctor_set(v___x_1103_, 0, v___x_1152_);
v___x_1154_ = v___x_1103_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_r_1094_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_r_1088_);
v___x_1154_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_isSharedCheck_1161_ = !lean_is_exclusive(v_r_1088_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; 
v_unused_1162_ = lean_ctor_get(v_r_1088_, 4);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_r_1088_, 3);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_r_1088_, 2);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_r_1088_, 1);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_r_1088_, 0);
lean_dec(v_unused_1166_);
v___x_1156_ = v_r_1088_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v_r_1088_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 4, v___x_1154_);
lean_ctor_set(v___x_1156_, 3, v_l_1093_);
lean_ctor_set(v___x_1156_, 2, v_v_1092_);
lean_ctor_set(v___x_1156_, 1, v_k_1091_);
lean_ctor_set(v___x_1156_, 0, v___x_1150_);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_l_1093_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v___x_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec_ref_known(v_l_1093_, 5);
lean_del_object(v___x_1103_);
lean_dec(v_v_1092_);
lean_dec(v_k_1091_);
lean_dec(v_size_1090_);
lean_dec_ref_known(v_r_1088_, 5);
lean_dec(v_v_1086_);
lean_dec(v_k_1085_);
v___x_1168_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
v___x_1169_ = l_panic___redArg(v___x_1105_, v___x_1168_);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_del_object(v___x_1103_);
lean_dec(v_r_1094_);
lean_dec(v_v_1092_);
lean_dec(v_k_1091_);
lean_dec(v_size_1090_);
lean_dec_ref_known(v_r_1088_, 5);
lean_dec(v_v_1086_);
lean_dec(v_k_1085_);
v___x_1170_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
v___x_1171_ = l_panic___redArg(v___x_1105_, v___x_1170_);
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_size_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_size_1178_ = lean_ctor_get(v_r_1088_, 0);
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_add(v___x_1179_, v_size_1178_);
v___x_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v_k_1085_);
lean_ctor_set(v___x_1181_, 2, v_v_1086_);
lean_ctor_set(v___x_1181_, 3, v_l_1087_);
lean_ctor_set(v___x_1181_, 4, v_r_1088_);
return v___x_1181_;
}
}
else
{
if (lean_obj_tag(v_l_1087_) == 0)
{
lean_object* v_l_1182_; 
v_l_1182_ = lean_ctor_get(v_l_1087_, 3);
if (lean_obj_tag(v_l_1182_) == 0)
{
lean_object* v_r_1183_; 
lean_inc_ref(v_l_1182_);
v_r_1183_ = lean_ctor_get(v_l_1087_, 4);
lean_inc(v_r_1183_);
if (lean_obj_tag(v_r_1183_) == 0)
{
lean_object* v_size_1184_; lean_object* v_k_1185_; lean_object* v_v_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1209_; 
v_size_1184_ = lean_ctor_get(v_l_1087_, 0);
v_k_1185_ = lean_ctor_get(v_l_1087_, 1);
v_v_1186_ = lean_ctor_get(v_l_1087_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; lean_object* v_unused_1211_; 
v_unused_1210_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1211_);
v___x_1188_ = v_l_1087_;
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_v_1186_);
lean_inc(v_k_1185_);
lean_inc(v_size_1184_);
lean_dec(v_l_1087_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_size_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v_size_1190_ = lean_ctor_get(v_r_1183_, 0);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v___x_1191_, v_size_1184_);
lean_dec(v_size_1184_);
v___x_1193_ = lean_nat_add(v___x_1191_, v_size_1190_);
lean_inc_ref(v_r_1183_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 4, v_r_1088_);
lean_ctor_set(v___x_1188_, 3, v_r_1183_);
lean_ctor_set(v___x_1188_, 2, v_v_1086_);
lean_ctor_set(v___x_1188_, 1, v_k_1085_);
lean_ctor_set(v___x_1188_, 0, v___x_1193_);
v___x_1195_ = v___x_1188_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_r_1183_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_r_1088_);
v___x_1195_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_isSharedCheck_1202_ = !lean_is_exclusive(v_r_1183_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1203_ = lean_ctor_get(v_r_1183_, 4);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_r_1183_, 3);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_r_1183_, 2);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_r_1183_, 1);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_r_1183_, 0);
lean_dec(v_unused_1207_);
v___x_1197_ = v_r_1183_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_dec(v_r_1183_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 4, v___x_1195_);
lean_ctor_set(v___x_1197_, 3, v_l_1182_);
lean_ctor_set(v___x_1197_, 2, v_v_1186_);
lean_ctor_set(v___x_1197_, 1, v_k_1185_);
lean_ctor_set(v___x_1197_, 0, v___x_1192_);
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_k_1185_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_v_1186_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_l_1182_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v___x_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
else
{
lean_object* v_k_1212_; lean_object* v_v_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1223_; 
v_k_1212_ = lean_ctor_get(v_l_1087_, 1);
v_v_1213_ = lean_ctor_get(v_l_1087_, 2);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; lean_object* v_unused_1225_; lean_object* v_unused_1226_; 
v_unused_1224_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_l_1087_, 0);
lean_dec(v_unused_1226_);
v___x_1215_ = v_l_1087_;
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_v_1213_);
lean_inc(v_k_1212_);
lean_dec(v_l_1087_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = lean_unsigned_to_nat(3u);
v___x_1218_ = lean_unsigned_to_nat(1u);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 3, v_r_1183_);
lean_ctor_set(v___x_1215_, 2, v_v_1086_);
lean_ctor_set(v___x_1215_, 1, v_k_1085_);
lean_ctor_set(v___x_1215_, 0, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_r_1183_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_r_1183_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1217_);
lean_ctor_set(v___x_1221_, 1, v_k_1212_);
lean_ctor_set(v___x_1221_, 2, v_v_1213_);
lean_ctor_set(v___x_1221_, 3, v_l_1182_);
lean_ctor_set(v___x_1221_, 4, v___x_1220_);
return v___x_1221_;
}
}
}
}
else
{
lean_object* v_r_1227_; 
v_r_1227_ = lean_ctor_get(v_l_1087_, 4);
lean_inc(v_r_1227_);
if (lean_obj_tag(v_r_1227_) == 0)
{
lean_object* v_k_1228_; lean_object* v_v_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1251_; 
lean_inc(v_l_1182_);
v_k_1228_ = lean_ctor_get(v_l_1087_, 1);
v_v_1229_ = lean_ctor_get(v_l_1087_, 2);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; lean_object* v_unused_1253_; lean_object* v_unused_1254_; 
v_unused_1252_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v_l_1087_, 0);
lean_dec(v_unused_1254_);
v___x_1231_ = v_l_1087_;
v_isShared_1232_ = v_isSharedCheck_1251_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_v_1229_);
lean_inc(v_k_1228_);
lean_dec(v_l_1087_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1251_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_k_1233_; lean_object* v_v_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1247_; 
v_k_1233_ = lean_ctor_get(v_r_1227_, 1);
v_v_1234_ = lean_ctor_get(v_r_1227_, 2);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_r_1227_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; lean_object* v_unused_1249_; lean_object* v_unused_1250_; 
v_unused_1248_ = lean_ctor_get(v_r_1227_, 4);
lean_dec(v_unused_1248_);
v_unused_1249_ = lean_ctor_get(v_r_1227_, 3);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v_r_1227_, 0);
lean_dec(v_unused_1250_);
v___x_1236_ = v_r_1227_;
v_isShared_1237_ = v_isSharedCheck_1247_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_v_1234_);
lean_inc(v_k_1233_);
lean_dec(v_r_1227_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1247_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1238_ = lean_unsigned_to_nat(3u);
v___x_1239_ = lean_unsigned_to_nat(1u);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 4, v_l_1182_);
lean_ctor_set(v___x_1236_, 3, v_l_1182_);
lean_ctor_set(v___x_1236_, 2, v_v_1229_);
lean_ctor_set(v___x_1236_, 1, v_k_1228_);
lean_ctor_set(v___x_1236_, 0, v___x_1239_);
v___x_1241_ = v___x_1236_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_l_1182_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_l_1182_);
v___x_1241_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v_l_1182_);
lean_ctor_set(v___x_1231_, 2, v_v_1086_);
lean_ctor_set(v___x_1231_, 1, v_k_1085_);
lean_ctor_set(v___x_1231_, 0, v___x_1239_);
v___x_1243_ = v___x_1231_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_l_1182_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_l_1182_);
v___x_1243_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1238_);
lean_ctor_set(v___x_1244_, 1, v_k_1233_);
lean_ctor_set(v___x_1244_, 2, v_v_1234_);
lean_ctor_set(v___x_1244_, 3, v___x_1241_);
lean_ctor_set(v___x_1244_, 4, v___x_1243_);
return v___x_1244_;
}
}
}
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_unsigned_to_nat(2u);
v___x_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_k_1085_);
lean_ctor_set(v___x_1256_, 2, v_v_1086_);
lean_ctor_set(v___x_1256_, 3, v_l_1087_);
lean_ctor_set(v___x_1256_, 4, v_r_1227_);
return v___x_1256_;
}
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_k_1085_);
lean_ctor_set(v___x_1258_, 2, v_v_1086_);
lean_ctor_set(v___x_1258_, 3, v_l_1087_);
lean_ctor_set(v___x_1258_, 4, v_l_1087_);
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceL_x21(lean_object* v_00_u03b1_1259_, lean_object* v_00_u03b2_1260_, lean_object* v_k_1261_, lean_object* v_v_1262_, lean_object* v_l_1263_, lean_object* v_r_1264_){
_start:
{
if (lean_obj_tag(v_r_1264_) == 0)
{
if (lean_obj_tag(v_l_1263_) == 0)
{
lean_object* v_size_1265_; lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_l_1269_; lean_object* v_r_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_size_1265_ = lean_ctor_get(v_r_1264_, 0);
v_size_1266_ = lean_ctor_get(v_l_1263_, 0);
v_k_1267_ = lean_ctor_get(v_l_1263_, 1);
v_v_1268_ = lean_ctor_get(v_l_1263_, 2);
v_l_1269_ = lean_ctor_get(v_l_1263_, 3);
v_r_1270_ = lean_ctor_get(v_l_1263_, 4);
lean_inc(v_r_1270_);
v___x_1271_ = lean_unsigned_to_nat(3u);
v___x_1272_ = lean_nat_mul(v___x_1271_, v_size_1265_);
v___x_1273_ = lean_nat_dec_lt(v___x_1272_, v_size_1266_);
lean_dec(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec(v_r_1270_);
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = lean_nat_add(v___x_1274_, v_size_1266_);
v___x_1276_ = lean_nat_add(v___x_1275_, v_size_1265_);
lean_dec(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_k_1261_);
lean_ctor_set(v___x_1277_, 2, v_v_1262_);
lean_ctor_set(v___x_1277_, 3, v_l_1263_);
lean_ctor_set(v___x_1277_, 4, v_r_1264_);
return v___x_1277_;
}
else
{
lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1348_; 
lean_inc(v_l_1269_);
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
lean_inc(v_size_1266_);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_l_1263_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; lean_object* v_unused_1350_; lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; 
v_unused_1349_ = lean_ctor_get(v_l_1263_, 4);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_l_1263_, 3);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_l_1263_, 2);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_l_1263_, 1);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_l_1263_, 0);
lean_dec(v_unused_1353_);
v___x_1279_ = v_l_1263_;
v_isShared_1280_ = v_isSharedCheck_1348_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v_l_1263_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1348_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_box(1);
if (lean_obj_tag(v_l_1269_) == 0)
{
if (lean_obj_tag(v_r_1270_) == 0)
{
lean_object* v_size_1282_; lean_object* v_size_1283_; lean_object* v_k_1284_; lean_object* v_v_1285_; lean_object* v_l_1286_; lean_object* v_r_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_size_1282_ = lean_ctor_get(v_l_1269_, 0);
v_size_1283_ = lean_ctor_get(v_r_1270_, 0);
v_k_1284_ = lean_ctor_get(v_r_1270_, 1);
v_v_1285_ = lean_ctor_get(v_r_1270_, 2);
v_l_1286_ = lean_ctor_get(v_r_1270_, 3);
v_r_1287_ = lean_ctor_get(v_r_1270_, 4);
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
v_isSharedCheck_1318_ = !lean_is_exclusive(v_r_1270_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; 
v_unused_1319_ = lean_ctor_get(v_r_1270_, 4);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_r_1270_, 3);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_r_1270_, 2);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_r_1270_, 1);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_r_1270_, 0);
lean_dec(v_unused_1323_);
v___x_1292_ = v_r_1270_;
v_isShared_1293_ = v_isSharedCheck_1318_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v_r_1270_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1318_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___x_1308_; lean_object* v___y_1310_; 
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v___x_1294_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1296_ = lean_nat_add(v___x_1295_, v_size_1265_);
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
v___x_1301_ = lean_nat_add(v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec(v___y_1299_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_r_1264_);
lean_ctor_set(v___x_1292_, 3, v_r_1287_);
lean_ctor_set(v___x_1292_, 2, v_v_1262_);
lean_ctor_set(v___x_1292_, 1, v_k_1261_);
lean_ctor_set(v___x_1292_, 0, v___x_1301_);
v___x_1303_ = v___x_1292_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_r_1287_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v_r_1264_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v___x_1303_);
lean_ctor_set(v___x_1279_, 3, v___y_1298_);
lean_ctor_set(v___x_1279_, 2, v_v_1285_);
lean_ctor_set(v___x_1279_, 1, v_k_1284_);
lean_ctor_set(v___x_1279_, 0, v___x_1296_);
v___x_1305_ = v___x_1279_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_k_1284_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_v_1285_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v___y_1298_);
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
lean_ctor_set(v___x_1312_, 1, v_k_1267_);
lean_ctor_set(v___x_1312_, 2, v_v_1268_);
lean_ctor_set(v___x_1312_, 3, v_l_1269_);
lean_ctor_set(v___x_1312_, 4, v_l_1286_);
v___x_1313_ = lean_nat_add(v___x_1294_, v_size_1265_);
if (lean_obj_tag(v_r_1287_) == 0)
{
lean_object* v_size_1314_; 
v_size_1314_ = lean_ctor_get(v_r_1287_, 0);
lean_inc(v_size_1314_);
v___y_1298_ = v___x_1312_;
v___y_1299_ = v___x_1313_;
v___y_1300_ = v_size_1314_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___y_1298_ = v___x_1312_;
v___y_1299_ = v___x_1313_;
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
v___x_1325_ = lean_nat_add(v___x_1324_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1326_ = lean_nat_add(v___x_1325_, v_size_1265_);
lean_dec(v___x_1325_);
v___x_1327_ = lean_nat_add(v___x_1324_, v_size_1265_);
v___x_1328_ = lean_nat_add(v___x_1327_, v_size_1283_);
lean_dec(v___x_1327_);
lean_inc_ref(v_r_1264_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v_r_1264_);
lean_ctor_set(v___x_1279_, 3, v_r_1270_);
lean_ctor_set(v___x_1279_, 2, v_v_1262_);
lean_ctor_set(v___x_1279_, 1, v_k_1261_);
lean_ctor_set(v___x_1279_, 0, v___x_1328_);
v___x_1330_ = v___x_1279_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_r_1270_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_r_1264_);
v___x_1330_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_isSharedCheck_1337_ = !lean_is_exclusive(v_r_1264_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; lean_object* v_unused_1339_; lean_object* v_unused_1340_; lean_object* v_unused_1341_; lean_object* v_unused_1342_; 
v_unused_1338_ = lean_ctor_get(v_r_1264_, 4);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_r_1264_, 3);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_r_1264_, 2);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v_r_1264_, 1);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_r_1264_, 0);
lean_dec(v_unused_1342_);
v___x_1332_ = v_r_1264_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v_r_1264_);
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
lean_ctor_set(v___x_1332_, 3, v_l_1269_);
lean_ctor_set(v___x_1332_, 2, v_v_1268_);
lean_ctor_set(v___x_1332_, 1, v_k_1267_);
lean_ctor_set(v___x_1332_, 0, v___x_1326_);
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_l_1269_);
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
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref_known(v_l_1269_, 5);
lean_del_object(v___x_1279_);
lean_dec(v_v_1268_);
lean_dec(v_k_1267_);
lean_dec(v_size_1266_);
lean_dec_ref_known(v_r_1264_, 5);
lean_dec(v_v_1262_);
lean_dec(v_k_1261_);
v___x_1344_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__3);
v___x_1345_ = l_panic___redArg(v___x_1281_, v___x_1344_);
return v___x_1345_;
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_del_object(v___x_1279_);
lean_dec(v_r_1270_);
lean_dec(v_v_1268_);
lean_dec(v_k_1267_);
lean_dec(v_size_1266_);
lean_dec_ref_known(v_r_1264_, 5);
lean_dec(v_v_1262_);
lean_dec(v_k_1261_);
v___x_1346_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__4);
v___x_1347_ = l_panic___redArg(v___x_1281_, v___x_1346_);
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_size_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_size_1354_ = lean_ctor_get(v_r_1264_, 0);
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_add(v___x_1355_, v_size_1354_);
v___x_1357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v_k_1261_);
lean_ctor_set(v___x_1357_, 2, v_v_1262_);
lean_ctor_set(v___x_1357_, 3, v_l_1263_);
lean_ctor_set(v___x_1357_, 4, v_r_1264_);
return v___x_1357_;
}
}
else
{
if (lean_obj_tag(v_l_1263_) == 0)
{
lean_object* v_l_1358_; 
v_l_1358_ = lean_ctor_get(v_l_1263_, 3);
if (lean_obj_tag(v_l_1358_) == 0)
{
lean_object* v_r_1359_; 
lean_inc_ref(v_l_1358_);
v_r_1359_ = lean_ctor_get(v_l_1263_, 4);
lean_inc(v_r_1359_);
if (lean_obj_tag(v_r_1359_) == 0)
{
lean_object* v_size_1360_; lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1385_; 
v_size_1360_ = lean_ctor_get(v_l_1263_, 0);
v_k_1361_ = lean_ctor_get(v_l_1263_, 1);
v_v_1362_ = lean_ctor_get(v_l_1263_, 2);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_l_1263_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; lean_object* v_unused_1387_; 
v_unused_1386_ = lean_ctor_get(v_l_1263_, 4);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_l_1263_, 3);
lean_dec(v_unused_1387_);
v___x_1364_ = v_l_1263_;
v_isShared_1365_ = v_isSharedCheck_1385_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
lean_inc(v_size_1360_);
lean_dec(v_l_1263_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1385_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_size_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v_size_1366_ = lean_ctor_get(v_r_1359_, 0);
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v___x_1367_, v_size_1360_);
lean_dec(v_size_1360_);
v___x_1369_ = lean_nat_add(v___x_1367_, v_size_1366_);
lean_inc_ref(v_r_1359_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_r_1264_);
lean_ctor_set(v___x_1364_, 3, v_r_1359_);
lean_ctor_set(v___x_1364_, 2, v_v_1262_);
lean_ctor_set(v___x_1364_, 1, v_k_1261_);
lean_ctor_set(v___x_1364_, 0, v___x_1369_);
v___x_1371_ = v___x_1364_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_r_1359_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_r_1264_);
v___x_1371_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v_r_1359_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; lean_object* v_unused_1380_; lean_object* v_unused_1381_; lean_object* v_unused_1382_; lean_object* v_unused_1383_; 
v_unused_1379_ = lean_ctor_get(v_r_1359_, 4);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_r_1359_, 3);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_r_1359_, 2);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_r_1359_, 1);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_r_1359_, 0);
lean_dec(v_unused_1383_);
v___x_1373_ = v_r_1359_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v_r_1359_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v___x_1371_);
lean_ctor_set(v___x_1373_, 3, v_l_1358_);
lean_ctor_set(v___x_1373_, 2, v_v_1362_);
lean_ctor_set(v___x_1373_, 1, v_k_1361_);
lean_ctor_set(v___x_1373_, 0, v___x_1368_);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_l_1358_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v___x_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1399_; 
v_k_1388_ = lean_ctor_get(v_l_1263_, 1);
v_v_1389_ = lean_ctor_get(v_l_1263_, 2);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_l_1263_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; lean_object* v_unused_1401_; lean_object* v_unused_1402_; 
v_unused_1400_ = lean_ctor_get(v_l_1263_, 4);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_l_1263_, 3);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_l_1263_, 0);
lean_dec(v_unused_1402_);
v___x_1391_ = v_l_1263_;
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_v_1389_);
lean_inc(v_k_1388_);
lean_dec(v_l_1263_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1393_ = lean_unsigned_to_nat(3u);
v___x_1394_ = lean_unsigned_to_nat(1u);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 3, v_r_1359_);
lean_ctor_set(v___x_1391_, 2, v_v_1262_);
lean_ctor_set(v___x_1391_, 1, v_k_1261_);
lean_ctor_set(v___x_1391_, 0, v___x_1394_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_r_1359_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_r_1359_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1393_);
lean_ctor_set(v___x_1397_, 1, v_k_1388_);
lean_ctor_set(v___x_1397_, 2, v_v_1389_);
lean_ctor_set(v___x_1397_, 3, v_l_1358_);
lean_ctor_set(v___x_1397_, 4, v___x_1396_);
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_r_1403_; 
v_r_1403_ = lean_ctor_get(v_l_1263_, 4);
lean_inc(v_r_1403_);
if (lean_obj_tag(v_r_1403_) == 0)
{
lean_object* v_k_1404_; lean_object* v_v_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1427_; 
lean_inc(v_l_1358_);
v_k_1404_ = lean_ctor_get(v_l_1263_, 1);
v_v_1405_ = lean_ctor_get(v_l_1263_, 2);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_l_1263_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; 
v_unused_1428_ = lean_ctor_get(v_l_1263_, 4);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_l_1263_, 3);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_l_1263_, 0);
lean_dec(v_unused_1430_);
v___x_1407_ = v_l_1263_;
v_isShared_1408_ = v_isSharedCheck_1427_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_v_1405_);
lean_inc(v_k_1404_);
lean_dec(v_l_1263_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1427_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1423_; 
v_k_1409_ = lean_ctor_get(v_r_1403_, 1);
v_v_1410_ = lean_ctor_get(v_r_1403_, 2);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_r_1403_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; lean_object* v_unused_1425_; lean_object* v_unused_1426_; 
v_unused_1424_ = lean_ctor_get(v_r_1403_, 4);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_r_1403_, 3);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_r_1403_, 0);
lean_dec(v_unused_1426_);
v___x_1412_ = v_r_1403_;
v_isShared_1413_ = v_isSharedCheck_1423_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_v_1410_);
lean_inc(v_k_1409_);
lean_dec(v_r_1403_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1423_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = lean_unsigned_to_nat(3u);
v___x_1415_ = lean_unsigned_to_nat(1u);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_l_1358_);
lean_ctor_set(v___x_1412_, 3, v_l_1358_);
lean_ctor_set(v___x_1412_, 2, v_v_1405_);
lean_ctor_set(v___x_1412_, 1, v_k_1404_);
lean_ctor_set(v___x_1412_, 0, v___x_1415_);
v___x_1417_ = v___x_1412_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_l_1358_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_l_1358_);
v___x_1417_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 4, v_l_1358_);
lean_ctor_set(v___x_1407_, 2, v_v_1262_);
lean_ctor_set(v___x_1407_, 1, v_k_1261_);
lean_ctor_set(v___x_1407_, 0, v___x_1415_);
v___x_1419_ = v___x_1407_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_l_1358_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_l_1358_);
v___x_1419_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1414_);
lean_ctor_set(v___x_1420_, 1, v_k_1409_);
lean_ctor_set(v___x_1420_, 2, v_v_1410_);
lean_ctor_set(v___x_1420_, 3, v___x_1417_);
lean_ctor_set(v___x_1420_, 4, v___x_1419_);
return v___x_1420_;
}
}
}
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(2u);
v___x_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_k_1261_);
lean_ctor_set(v___x_1432_, 2, v_v_1262_);
lean_ctor_set(v___x_1432_, 3, v_l_1263_);
lean_ctor_set(v___x_1432_, 4, v_r_1403_);
return v___x_1432_;
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v_k_1261_);
lean_ctor_set(v___x_1434_, 2, v_v_1262_);
lean_ctor_set(v___x_1434_, 3, v_l_1263_);
lean_ctor_set(v___x_1434_, 4, v_l_1263_);
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR___redArg(lean_object* v_k_1435_, lean_object* v_v_1436_, lean_object* v_l_1437_, lean_object* v_r_1438_){
_start:
{
if (lean_obj_tag(v_l_1437_) == 0)
{
if (lean_obj_tag(v_r_1438_) == 0)
{
lean_object* v_size_1439_; lean_object* v_size_1440_; lean_object* v_k_1441_; lean_object* v_v_1442_; lean_object* v_l_1443_; lean_object* v_r_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_size_1439_ = lean_ctor_get(v_l_1437_, 0);
v_size_1440_ = lean_ctor_get(v_r_1438_, 0);
v_k_1441_ = lean_ctor_get(v_r_1438_, 1);
v_v_1442_ = lean_ctor_get(v_r_1438_, 2);
v_l_1443_ = lean_ctor_get(v_r_1438_, 3);
lean_inc(v_l_1443_);
v_r_1444_ = lean_ctor_get(v_r_1438_, 4);
v___x_1445_ = lean_unsigned_to_nat(3u);
v___x_1446_ = lean_nat_mul(v___x_1445_, v_size_1439_);
v___x_1447_ = lean_nat_dec_lt(v___x_1446_, v_size_1440_);
lean_dec(v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec(v_l_1443_);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v___x_1448_, v_size_1439_);
v___x_1450_ = lean_nat_add(v___x_1449_, v_size_1440_);
lean_dec(v___x_1449_);
v___x_1451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v_k_1435_);
lean_ctor_set(v___x_1451_, 2, v_v_1436_);
lean_ctor_set(v___x_1451_, 3, v_l_1437_);
lean_ctor_set(v___x_1451_, 4, v_r_1438_);
return v___x_1451_;
}
else
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1515_; 
lean_inc(v_r_1444_);
lean_inc(v_v_1442_);
lean_inc(v_k_1441_);
lean_inc(v_size_1440_);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_r_1438_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; 
v_unused_1516_ = lean_ctor_get(v_r_1438_, 4);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1438_, 3);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_r_1438_, 2);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_r_1438_, 1);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1438_, 0);
lean_dec(v_unused_1520_);
v___x_1453_ = v_r_1438_;
v_isShared_1454_ = v_isSharedCheck_1515_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v_r_1438_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1515_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_size_1455_; lean_object* v_k_1456_; lean_object* v_v_1457_; lean_object* v_l_1458_; lean_object* v_r_1459_; lean_object* v_size_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_size_1455_ = lean_ctor_get(v_l_1443_, 0);
v_k_1456_ = lean_ctor_get(v_l_1443_, 1);
v_v_1457_ = lean_ctor_get(v_l_1443_, 2);
v_l_1458_ = lean_ctor_get(v_l_1443_, 3);
v_r_1459_ = lean_ctor_get(v_l_1443_, 4);
v_size_1460_ = lean_ctor_get(v_r_1444_, 0);
v___x_1461_ = lean_unsigned_to_nat(2u);
v___x_1462_ = lean_nat_mul(v___x_1461_, v_size_1460_);
v___x_1463_ = lean_nat_dec_lt(v_size_1455_, v___x_1462_);
lean_dec(v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1490_; 
lean_inc(v_r_1459_);
lean_inc(v_l_1458_);
lean_inc(v_v_1457_);
lean_inc(v_k_1456_);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_l_1443_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1491_ = lean_ctor_get(v_l_1443_, 4);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_l_1443_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_l_1443_, 2);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1443_, 1);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1443_, 0);
lean_dec(v_unused_1495_);
v___x_1465_ = v_l_1443_;
v_isShared_1466_ = v_isSharedCheck_1490_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v_l_1443_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1490_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1482_; 
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v___x_1467_, v_size_1439_);
v___x_1469_ = lean_nat_add(v___x_1468_, v_size_1440_);
lean_dec(v_size_1440_);
if (lean_obj_tag(v_l_1458_) == 0)
{
lean_object* v_size_1488_; 
v_size_1488_ = lean_ctor_get(v_l_1458_, 0);
lean_inc(v_size_1488_);
v___y_1482_ = v_size_1488_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___y_1482_ = v___x_1489_;
goto v___jp_1481_;
}
v___jp_1470_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_nat_add(v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v_r_1444_);
lean_ctor_set(v___x_1465_, 3, v_r_1459_);
lean_ctor_set(v___x_1465_, 2, v_v_1442_);
lean_ctor_set(v___x_1465_, 1, v_k_1441_);
lean_ctor_set(v___x_1465_, 0, v___x_1474_);
v___x_1476_ = v___x_1465_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1441_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1442_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1459_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1444_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v___x_1476_);
lean_ctor_set(v___x_1453_, 3, v___y_1471_);
lean_ctor_set(v___x_1453_, 2, v_v_1457_);
lean_ctor_set(v___x_1453_, 1, v_k_1456_);
lean_ctor_set(v___x_1453_, 0, v___x_1469_);
v___x_1478_ = v___x_1453_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1456_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1457_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
v___jp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = lean_nat_add(v___x_1468_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec(v___x_1468_);
v___x_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v_k_1435_);
lean_ctor_set(v___x_1484_, 2, v_v_1436_);
lean_ctor_set(v___x_1484_, 3, v_l_1437_);
lean_ctor_set(v___x_1484_, 4, v_l_1458_);
v___x_1485_ = lean_nat_add(v___x_1467_, v_size_1460_);
if (lean_obj_tag(v_r_1459_) == 0)
{
lean_object* v_size_1486_; 
v_size_1486_ = lean_ctor_get(v_r_1459_, 0);
lean_inc(v_size_1486_);
v___y_1471_ = v___x_1484_;
v___y_1472_ = v___x_1485_;
v___y_1473_ = v_size_1486_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___y_1471_ = v___x_1484_;
v___y_1472_ = v___x_1485_;
v___y_1473_ = v___x_1487_;
goto v___jp_1470_;
}
}
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_add(v___x_1496_, v_size_1439_);
v___x_1498_ = lean_nat_add(v___x_1497_, v_size_1440_);
lean_dec(v_size_1440_);
v___x_1499_ = lean_nat_add(v___x_1497_, v_size_1455_);
lean_dec(v___x_1497_);
lean_inc_ref(v_l_1437_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v_l_1443_);
lean_ctor_set(v___x_1453_, 3, v_l_1437_);
lean_ctor_set(v___x_1453_, 2, v_v_1436_);
lean_ctor_set(v___x_1453_, 1, v_k_1435_);
lean_ctor_set(v___x_1453_, 0, v___x_1499_);
v___x_1501_ = v___x_1453_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_l_1443_);
v___x_1501_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_isSharedCheck_1508_ = !lean_is_exclusive(v_l_1437_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; 
v_unused_1509_ = lean_ctor_get(v_l_1437_, 4);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_l_1437_, 3);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_l_1437_, 2);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_l_1437_, 1);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1437_, 0);
lean_dec(v_unused_1513_);
v___x_1503_ = v_l_1437_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v_l_1437_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_r_1444_);
lean_ctor_set(v___x_1503_, 3, v___x_1501_);
lean_ctor_set(v___x_1503_, 2, v_v_1442_);
lean_ctor_set(v___x_1503_, 1, v_k_1441_);
lean_ctor_set(v___x_1503_, 0, v___x_1498_);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1441_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1442_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_r_1444_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_size_1521_ = lean_ctor_get(v_l_1437_, 0);
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_add(v___x_1522_, v_size_1521_);
v___x_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v_k_1435_);
lean_ctor_set(v___x_1524_, 2, v_v_1436_);
lean_ctor_set(v___x_1524_, 3, v_l_1437_);
lean_ctor_set(v___x_1524_, 4, v_r_1438_);
return v___x_1524_;
}
}
else
{
if (lean_obj_tag(v_r_1438_) == 0)
{
lean_object* v_l_1525_; 
v_l_1525_ = lean_ctor_get(v_r_1438_, 3);
lean_inc(v_l_1525_);
if (lean_obj_tag(v_l_1525_) == 0)
{
lean_object* v_r_1526_; lean_object* v_k_1527_; lean_object* v_v_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1550_; 
v_r_1526_ = lean_ctor_get(v_r_1438_, 4);
v_k_1527_ = lean_ctor_get(v_r_1438_, 1);
v_v_1528_ = lean_ctor_get(v_r_1438_, 2);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_r_1438_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1551_ = lean_ctor_get(v_r_1438_, 3);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_r_1438_, 0);
lean_dec(v_unused_1552_);
v___x_1530_ = v_r_1438_;
v_isShared_1531_ = v_isSharedCheck_1550_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_r_1526_);
lean_inc(v_v_1528_);
lean_inc(v_k_1527_);
lean_dec(v_r_1438_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1550_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_k_1532_; lean_object* v_v_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1546_; 
v_k_1532_ = lean_ctor_get(v_l_1525_, 1);
v_v_1533_ = lean_ctor_get(v_l_1525_, 2);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_l_1525_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; lean_object* v_unused_1548_; lean_object* v_unused_1549_; 
v_unused_1547_ = lean_ctor_get(v_l_1525_, 4);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_l_1525_, 3);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_l_1525_, 0);
lean_dec(v_unused_1549_);
v___x_1535_ = v_l_1525_;
v_isShared_1536_ = v_isSharedCheck_1546_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_v_1533_);
lean_inc(v_k_1532_);
lean_dec(v_l_1525_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1546_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1537_ = lean_unsigned_to_nat(3u);
v___x_1538_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_r_1526_, 2);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 4, v_r_1526_);
lean_ctor_set(v___x_1535_, 3, v_r_1526_);
lean_ctor_set(v___x_1535_, 2, v_v_1436_);
lean_ctor_set(v___x_1535_, 1, v_k_1435_);
lean_ctor_set(v___x_1535_, 0, v___x_1538_);
v___x_1540_ = v___x_1535_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_r_1526_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_r_1526_);
v___x_1540_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
lean_inc(v_r_1526_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 3, v_r_1526_);
lean_ctor_set(v___x_1530_, 0, v___x_1538_);
v___x_1542_ = v___x_1530_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1527_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1528_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_r_1526_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_r_1526_);
v___x_1542_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1537_);
lean_ctor_set(v___x_1543_, 1, v_k_1532_);
lean_ctor_set(v___x_1543_, 2, v_v_1533_);
lean_ctor_set(v___x_1543_, 3, v___x_1540_);
lean_ctor_set(v___x_1543_, 4, v___x_1542_);
return v___x_1543_;
}
}
}
}
}
else
{
lean_object* v_r_1553_; 
v_r_1553_ = lean_ctor_get(v_r_1438_, 4);
lean_inc(v_r_1553_);
if (lean_obj_tag(v_r_1553_) == 0)
{
lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1565_; 
v_k_1554_ = lean_ctor_get(v_r_1438_, 1);
v_v_1555_ = lean_ctor_get(v_r_1438_, 2);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_r_1438_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; lean_object* v_unused_1567_; lean_object* v_unused_1568_; 
v_unused_1566_ = lean_ctor_get(v_r_1438_, 4);
lean_dec(v_unused_1566_);
v_unused_1567_ = lean_ctor_get(v_r_1438_, 3);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_r_1438_, 0);
lean_dec(v_unused_1568_);
v___x_1557_ = v_r_1438_;
v_isShared_1558_ = v_isSharedCheck_1565_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
lean_dec(v_r_1438_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1565_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1559_ = lean_unsigned_to_nat(3u);
v___x_1560_ = lean_unsigned_to_nat(1u);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v_l_1525_);
lean_ctor_set(v___x_1557_, 2, v_v_1436_);
lean_ctor_set(v___x_1557_, 1, v_k_1435_);
lean_ctor_set(v___x_1557_, 0, v___x_1560_);
v___x_1562_ = v___x_1557_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_l_1525_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_l_1525_);
v___x_1562_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1559_);
lean_ctor_set(v___x_1563_, 1, v_k_1554_);
lean_ctor_set(v___x_1563_, 2, v_v_1555_);
lean_ctor_set(v___x_1563_, 3, v___x_1562_);
lean_ctor_set(v___x_1563_, 4, v_r_1553_);
return v___x_1563_;
}
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_unsigned_to_nat(2u);
v___x_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v_k_1435_);
lean_ctor_set(v___x_1570_, 2, v_v_1436_);
lean_ctor_set(v___x_1570_, 3, v_r_1553_);
lean_ctor_set(v___x_1570_, 4, v_r_1438_);
return v___x_1570_;
}
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_unsigned_to_nat(1u);
v___x_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_k_1435_);
lean_ctor_set(v___x_1572_, 2, v_v_1436_);
lean_ctor_set(v___x_1572_, 3, v_r_1438_);
lean_ctor_set(v___x_1572_, 4, v_r_1438_);
return v___x_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR(lean_object* v_00_u03b1_1573_, lean_object* v_00_u03b2_1574_, lean_object* v_k_1575_, lean_object* v_v_1576_, lean_object* v_l_1577_, lean_object* v_r_1578_, lean_object* v_hlb_1579_, lean_object* v_hrb_1580_, lean_object* v_hlr_1581_){
_start:
{
if (lean_obj_tag(v_l_1577_) == 0)
{
if (lean_obj_tag(v_r_1578_) == 0)
{
lean_object* v_size_1582_; lean_object* v_size_1583_; lean_object* v_k_1584_; lean_object* v_v_1585_; lean_object* v_l_1586_; lean_object* v_r_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_size_1582_ = lean_ctor_get(v_l_1577_, 0);
v_size_1583_ = lean_ctor_get(v_r_1578_, 0);
v_k_1584_ = lean_ctor_get(v_r_1578_, 1);
v_v_1585_ = lean_ctor_get(v_r_1578_, 2);
v_l_1586_ = lean_ctor_get(v_r_1578_, 3);
lean_inc(v_l_1586_);
v_r_1587_ = lean_ctor_get(v_r_1578_, 4);
v___x_1588_ = lean_unsigned_to_nat(3u);
v___x_1589_ = lean_nat_mul(v___x_1588_, v_size_1582_);
v___x_1590_ = lean_nat_dec_lt(v___x_1589_, v_size_1583_);
lean_dec(v___x_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_l_1586_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_add(v___x_1591_, v_size_1582_);
v___x_1593_ = lean_nat_add(v___x_1592_, v_size_1583_);
lean_dec(v___x_1592_);
v___x_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_k_1575_);
lean_ctor_set(v___x_1594_, 2, v_v_1576_);
lean_ctor_set(v___x_1594_, 3, v_l_1577_);
lean_ctor_set(v___x_1594_, 4, v_r_1578_);
return v___x_1594_;
}
else
{
lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1658_; 
lean_inc(v_r_1587_);
lean_inc(v_v_1585_);
lean_inc(v_k_1584_);
lean_inc(v_size_1583_);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_r_1578_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1659_ = lean_ctor_get(v_r_1578_, 4);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_r_1578_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_r_1578_, 2);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_r_1578_, 1);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_r_1578_, 0);
lean_dec(v_unused_1663_);
v___x_1596_ = v_r_1578_;
v_isShared_1597_ = v_isSharedCheck_1658_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_r_1578_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1658_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_size_1598_; lean_object* v_k_1599_; lean_object* v_v_1600_; lean_object* v_l_1601_; lean_object* v_r_1602_; lean_object* v_size_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_size_1598_ = lean_ctor_get(v_l_1586_, 0);
v_k_1599_ = lean_ctor_get(v_l_1586_, 1);
v_v_1600_ = lean_ctor_get(v_l_1586_, 2);
v_l_1601_ = lean_ctor_get(v_l_1586_, 3);
v_r_1602_ = lean_ctor_get(v_l_1586_, 4);
v_size_1603_ = lean_ctor_get(v_r_1587_, 0);
v___x_1604_ = lean_unsigned_to_nat(2u);
v___x_1605_ = lean_nat_mul(v___x_1604_, v_size_1603_);
v___x_1606_ = lean_nat_dec_lt(v_size_1598_, v___x_1605_);
lean_dec(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1633_; 
lean_inc(v_r_1602_);
lean_inc(v_l_1601_);
lean_inc(v_v_1600_);
lean_inc(v_k_1599_);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_l_1586_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; 
v_unused_1634_ = lean_ctor_get(v_l_1586_, 4);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_l_1586_, 3);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_l_1586_, 2);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_l_1586_, 1);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_l_1586_, 0);
lean_dec(v_unused_1638_);
v___x_1608_ = v_l_1586_;
v_isShared_1609_ = v_isSharedCheck_1633_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v_l_1586_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1633_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1625_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_add(v___x_1610_, v_size_1582_);
v___x_1612_ = lean_nat_add(v___x_1611_, v_size_1583_);
lean_dec(v_size_1583_);
if (lean_obj_tag(v_l_1601_) == 0)
{
lean_object* v_size_1631_; 
v_size_1631_ = lean_ctor_get(v_l_1601_, 0);
lean_inc(v_size_1631_);
v___y_1625_ = v_size_1631_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___y_1625_ = v___x_1632_;
goto v___jp_1624_;
}
v___jp_1613_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_nat_add(v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 4, v_r_1587_);
lean_ctor_set(v___x_1608_, 3, v_r_1602_);
lean_ctor_set(v___x_1608_, 2, v_v_1585_);
lean_ctor_set(v___x_1608_, 1, v_k_1584_);
lean_ctor_set(v___x_1608_, 0, v___x_1617_);
v___x_1619_ = v___x_1608_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1584_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1585_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_r_1602_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_r_1587_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v___x_1619_);
lean_ctor_set(v___x_1596_, 3, v___y_1614_);
lean_ctor_set(v___x_1596_, 2, v_v_1600_);
lean_ctor_set(v___x_1596_, 1, v_k_1599_);
lean_ctor_set(v___x_1596_, 0, v___x_1612_);
v___x_1621_ = v___x_1596_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1599_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1600_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v___y_1614_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_nat_add(v___x_1611_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec(v___x_1611_);
v___x_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_k_1575_);
lean_ctor_set(v___x_1627_, 2, v_v_1576_);
lean_ctor_set(v___x_1627_, 3, v_l_1577_);
lean_ctor_set(v___x_1627_, 4, v_l_1601_);
v___x_1628_ = lean_nat_add(v___x_1610_, v_size_1603_);
if (lean_obj_tag(v_r_1602_) == 0)
{
lean_object* v_size_1629_; 
v_size_1629_ = lean_ctor_get(v_r_1602_, 0);
lean_inc(v_size_1629_);
v___y_1614_ = v___x_1627_;
v___y_1615_ = v___x_1628_;
v___y_1616_ = v_size_1629_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___y_1614_ = v___x_1627_;
v___y_1615_ = v___x_1628_;
v___y_1616_ = v___x_1630_;
goto v___jp_1613_;
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_nat_add(v___x_1639_, v_size_1582_);
v___x_1641_ = lean_nat_add(v___x_1640_, v_size_1583_);
lean_dec(v_size_1583_);
v___x_1642_ = lean_nat_add(v___x_1640_, v_size_1598_);
lean_dec(v___x_1640_);
lean_inc_ref(v_l_1577_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v_l_1586_);
lean_ctor_set(v___x_1596_, 3, v_l_1577_);
lean_ctor_set(v___x_1596_, 2, v_v_1576_);
lean_ctor_set(v___x_1596_, 1, v_k_1575_);
lean_ctor_set(v___x_1596_, 0, v___x_1642_);
v___x_1644_ = v___x_1596_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_k_1575_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_v_1576_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_l_1577_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_l_1586_);
v___x_1644_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_isSharedCheck_1651_ = !lean_is_exclusive(v_l_1577_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; lean_object* v_unused_1653_; lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; 
v_unused_1652_ = lean_ctor_get(v_l_1577_, 4);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_l_1577_, 3);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_l_1577_, 2);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_l_1577_, 1);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_l_1577_, 0);
lean_dec(v_unused_1656_);
v___x_1646_ = v_l_1577_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_dec(v_l_1577_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 4, v_r_1587_);
lean_ctor_set(v___x_1646_, 3, v___x_1644_);
lean_ctor_set(v___x_1646_, 2, v_v_1585_);
lean_ctor_set(v___x_1646_, 1, v_k_1584_);
lean_ctor_set(v___x_1646_, 0, v___x_1641_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1584_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1585_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_r_1587_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_size_1664_ = lean_ctor_get(v_l_1577_, 0);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v___x_1665_, v_size_1664_);
v___x_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_k_1575_);
lean_ctor_set(v___x_1667_, 2, v_v_1576_);
lean_ctor_set(v___x_1667_, 3, v_l_1577_);
lean_ctor_set(v___x_1667_, 4, v_r_1578_);
return v___x_1667_;
}
}
else
{
if (lean_obj_tag(v_r_1578_) == 0)
{
lean_object* v_l_1668_; 
v_l_1668_ = lean_ctor_get(v_r_1578_, 3);
lean_inc(v_l_1668_);
if (lean_obj_tag(v_l_1668_) == 0)
{
lean_object* v_r_1669_; lean_object* v_k_1670_; lean_object* v_v_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1693_; 
v_r_1669_ = lean_ctor_get(v_r_1578_, 4);
v_k_1670_ = lean_ctor_get(v_r_1578_, 1);
v_v_1671_ = lean_ctor_get(v_r_1578_, 2);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_r_1578_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; lean_object* v_unused_1695_; 
v_unused_1694_ = lean_ctor_get(v_r_1578_, 3);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_r_1578_, 0);
lean_dec(v_unused_1695_);
v___x_1673_ = v_r_1578_;
v_isShared_1674_ = v_isSharedCheck_1693_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_r_1669_);
lean_inc(v_v_1671_);
lean_inc(v_k_1670_);
lean_dec(v_r_1578_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1693_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_k_1675_; lean_object* v_v_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1689_; 
v_k_1675_ = lean_ctor_get(v_l_1668_, 1);
v_v_1676_ = lean_ctor_get(v_l_1668_, 2);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_l_1668_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; 
v_unused_1690_ = lean_ctor_get(v_l_1668_, 4);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_l_1668_, 3);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_l_1668_, 0);
lean_dec(v_unused_1692_);
v___x_1678_ = v_l_1668_;
v_isShared_1679_ = v_isSharedCheck_1689_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_v_1676_);
lean_inc(v_k_1675_);
lean_dec(v_l_1668_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1689_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1680_ = lean_unsigned_to_nat(3u);
v___x_1681_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_r_1669_, 2);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 4, v_r_1669_);
lean_ctor_set(v___x_1678_, 3, v_r_1669_);
lean_ctor_set(v___x_1678_, 2, v_v_1576_);
lean_ctor_set(v___x_1678_, 1, v_k_1575_);
lean_ctor_set(v___x_1678_, 0, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1575_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1576_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_r_1669_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_r_1669_);
v___x_1683_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
lean_inc(v_r_1669_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 3, v_r_1669_);
lean_ctor_set(v___x_1673_, 0, v___x_1681_);
v___x_1685_ = v___x_1673_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1670_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1671_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_r_1669_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_r_1669_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1680_);
lean_ctor_set(v___x_1686_, 1, v_k_1675_);
lean_ctor_set(v___x_1686_, 2, v_v_1676_);
lean_ctor_set(v___x_1686_, 3, v___x_1683_);
lean_ctor_set(v___x_1686_, 4, v___x_1685_);
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v_r_1696_; 
v_r_1696_ = lean_ctor_get(v_r_1578_, 4);
lean_inc(v_r_1696_);
if (lean_obj_tag(v_r_1696_) == 0)
{
lean_object* v_k_1697_; lean_object* v_v_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1708_; 
v_k_1697_ = lean_ctor_get(v_r_1578_, 1);
v_v_1698_ = lean_ctor_get(v_r_1578_, 2);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_r_1578_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; 
v_unused_1709_ = lean_ctor_get(v_r_1578_, 4);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_r_1578_, 3);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_r_1578_, 0);
lean_dec(v_unused_1711_);
v___x_1700_ = v_r_1578_;
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_v_1698_);
lean_inc(v_k_1697_);
lean_dec(v_r_1578_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1702_ = lean_unsigned_to_nat(3u);
v___x_1703_ = lean_unsigned_to_nat(1u);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 4, v_l_1668_);
lean_ctor_set(v___x_1700_, 2, v_v_1576_);
lean_ctor_set(v___x_1700_, 1, v_k_1575_);
lean_ctor_set(v___x_1700_, 0, v___x_1703_);
v___x_1705_ = v___x_1700_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_k_1575_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_v_1576_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_l_1668_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_l_1668_);
v___x_1705_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1702_);
lean_ctor_set(v___x_1706_, 1, v_k_1697_);
lean_ctor_set(v___x_1706_, 2, v_v_1698_);
lean_ctor_set(v___x_1706_, 3, v___x_1705_);
lean_ctor_set(v___x_1706_, 4, v_r_1696_);
return v___x_1706_;
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_unsigned_to_nat(2u);
v___x_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v_k_1575_);
lean_ctor_set(v___x_1713_, 2, v_v_1576_);
lean_ctor_set(v___x_1713_, 3, v_r_1696_);
lean_ctor_set(v___x_1713_, 4, v_r_1578_);
return v___x_1713_;
}
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v_k_1575_);
lean_ctor_set(v___x_1715_, 2, v_v_1576_);
lean_ctor_set(v___x_1715_, 3, v_r_1578_);
lean_ctor_set(v___x_1715_, 4, v_r_1578_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase___redArg(lean_object* v_k_1716_, lean_object* v_v_1717_, lean_object* v_l_1718_, lean_object* v_r_1719_){
_start:
{
if (lean_obj_tag(v_l_1718_) == 0)
{
if (lean_obj_tag(v_r_1719_) == 0)
{
lean_object* v_size_1720_; lean_object* v_size_1721_; lean_object* v_k_1722_; lean_object* v_v_1723_; lean_object* v_l_1724_; lean_object* v_r_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_size_1720_ = lean_ctor_get(v_l_1718_, 0);
v_size_1721_ = lean_ctor_get(v_r_1719_, 0);
v_k_1722_ = lean_ctor_get(v_r_1719_, 1);
v_v_1723_ = lean_ctor_get(v_r_1719_, 2);
v_l_1724_ = lean_ctor_get(v_r_1719_, 3);
lean_inc(v_l_1724_);
v_r_1725_ = lean_ctor_get(v_r_1719_, 4);
v___x_1726_ = lean_unsigned_to_nat(3u);
v___x_1727_ = lean_nat_mul(v___x_1726_, v_size_1720_);
v___x_1728_ = lean_nat_dec_lt(v___x_1727_, v_size_1721_);
lean_dec(v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v_l_1724_);
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1730_ = lean_nat_add(v___x_1729_, v_size_1720_);
v___x_1731_ = lean_nat_add(v___x_1730_, v_size_1721_);
lean_dec(v___x_1730_);
v___x_1732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v_k_1716_);
lean_ctor_set(v___x_1732_, 2, v_v_1717_);
lean_ctor_set(v___x_1732_, 3, v_l_1718_);
lean_ctor_set(v___x_1732_, 4, v_r_1719_);
return v___x_1732_;
}
else
{
lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1796_; 
lean_inc(v_r_1725_);
lean_inc(v_v_1723_);
lean_inc(v_k_1722_);
lean_inc(v_size_1721_);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_r_1719_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; 
v_unused_1797_ = lean_ctor_get(v_r_1719_, 4);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_r_1719_, 3);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_r_1719_, 2);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_r_1719_, 1);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_r_1719_, 0);
lean_dec(v_unused_1801_);
v___x_1734_ = v_r_1719_;
v_isShared_1735_ = v_isSharedCheck_1796_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v_r_1719_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1796_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_size_1736_; lean_object* v_k_1737_; lean_object* v_v_1738_; lean_object* v_l_1739_; lean_object* v_r_1740_; lean_object* v_size_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_size_1736_ = lean_ctor_get(v_l_1724_, 0);
v_k_1737_ = lean_ctor_get(v_l_1724_, 1);
v_v_1738_ = lean_ctor_get(v_l_1724_, 2);
v_l_1739_ = lean_ctor_get(v_l_1724_, 3);
v_r_1740_ = lean_ctor_get(v_l_1724_, 4);
v_size_1741_ = lean_ctor_get(v_r_1725_, 0);
v___x_1742_ = lean_unsigned_to_nat(2u);
v___x_1743_ = lean_nat_mul(v___x_1742_, v_size_1741_);
v___x_1744_ = lean_nat_dec_lt(v_size_1736_, v___x_1743_);
lean_dec(v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1771_; 
lean_inc(v_r_1740_);
lean_inc(v_l_1739_);
lean_inc(v_v_1738_);
lean_inc(v_k_1737_);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_l_1724_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; 
v_unused_1772_ = lean_ctor_get(v_l_1724_, 4);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_l_1724_, 3);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_l_1724_, 2);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_l_1724_, 1);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_l_1724_, 0);
lean_dec(v_unused_1776_);
v___x_1746_ = v_l_1724_;
v_isShared_1747_ = v_isSharedCheck_1771_;
goto v_resetjp_1745_;
}
else
{
lean_dec(v_l_1724_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1771_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1763_; 
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_add(v___x_1748_, v_size_1720_);
v___x_1750_ = lean_nat_add(v___x_1749_, v_size_1721_);
lean_dec(v_size_1721_);
if (lean_obj_tag(v_l_1739_) == 0)
{
lean_object* v_size_1769_; 
v_size_1769_ = lean_ctor_get(v_l_1739_, 0);
lean_inc(v_size_1769_);
v___y_1763_ = v_size_1769_;
goto v___jp_1762_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___y_1763_ = v___x_1770_;
goto v___jp_1762_;
}
v___jp_1751_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = lean_nat_add(v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec(v___y_1753_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 4, v_r_1725_);
lean_ctor_set(v___x_1746_, 3, v_r_1740_);
lean_ctor_set(v___x_1746_, 2, v_v_1723_);
lean_ctor_set(v___x_1746_, 1, v_k_1722_);
lean_ctor_set(v___x_1746_, 0, v___x_1755_);
v___x_1757_ = v___x_1746_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_k_1722_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_v_1723_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_r_1740_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_r_1725_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 4, v___x_1757_);
lean_ctor_set(v___x_1734_, 3, v___y_1752_);
lean_ctor_set(v___x_1734_, 2, v_v_1738_);
lean_ctor_set(v___x_1734_, 1, v_k_1737_);
lean_ctor_set(v___x_1734_, 0, v___x_1750_);
v___x_1759_ = v___x_1734_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_k_1737_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_v_1738_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v___y_1752_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
v___jp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_nat_add(v___x_1749_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec(v___x_1749_);
v___x_1765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v_k_1716_);
lean_ctor_set(v___x_1765_, 2, v_v_1717_);
lean_ctor_set(v___x_1765_, 3, v_l_1718_);
lean_ctor_set(v___x_1765_, 4, v_l_1739_);
v___x_1766_ = lean_nat_add(v___x_1748_, v_size_1741_);
if (lean_obj_tag(v_r_1740_) == 0)
{
lean_object* v_size_1767_; 
v_size_1767_ = lean_ctor_get(v_r_1740_, 0);
lean_inc(v_size_1767_);
v___y_1752_ = v___x_1765_;
v___y_1753_ = v___x_1766_;
v___y_1754_ = v_size_1767_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___y_1752_ = v___x_1765_;
v___y_1753_ = v___x_1766_;
v___y_1754_ = v___x_1768_;
goto v___jp_1751_;
}
}
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v___x_1777_, v_size_1720_);
v___x_1779_ = lean_nat_add(v___x_1778_, v_size_1721_);
lean_dec(v_size_1721_);
v___x_1780_ = lean_nat_add(v___x_1778_, v_size_1736_);
lean_dec(v___x_1778_);
lean_inc_ref(v_l_1718_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 4, v_l_1724_);
lean_ctor_set(v___x_1734_, 3, v_l_1718_);
lean_ctor_set(v___x_1734_, 2, v_v_1717_);
lean_ctor_set(v___x_1734_, 1, v_k_1716_);
lean_ctor_set(v___x_1734_, 0, v___x_1780_);
v___x_1782_ = v___x_1734_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_k_1716_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_v_1717_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_l_1718_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v_l_1724_);
v___x_1782_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_isSharedCheck_1789_ = !lean_is_exclusive(v_l_1718_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; lean_object* v_unused_1793_; lean_object* v_unused_1794_; 
v_unused_1790_ = lean_ctor_get(v_l_1718_, 4);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_l_1718_, 3);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_l_1718_, 2);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_l_1718_, 1);
lean_dec(v_unused_1793_);
v_unused_1794_ = lean_ctor_get(v_l_1718_, 0);
lean_dec(v_unused_1794_);
v___x_1784_ = v_l_1718_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_dec(v_l_1718_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 4, v_r_1725_);
lean_ctor_set(v___x_1784_, 3, v___x_1782_);
lean_ctor_set(v___x_1784_, 2, v_v_1723_);
lean_ctor_set(v___x_1784_, 1, v_k_1722_);
lean_ctor_set(v___x_1784_, 0, v___x_1779_);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_k_1722_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_v_1723_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_r_1725_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_size_1802_ = lean_ctor_get(v_l_1718_, 0);
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_nat_add(v___x_1803_, v_size_1802_);
v___x_1805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_k_1716_);
lean_ctor_set(v___x_1805_, 2, v_v_1717_);
lean_ctor_set(v___x_1805_, 3, v_l_1718_);
lean_ctor_set(v___x_1805_, 4, v_r_1719_);
return v___x_1805_;
}
}
else
{
if (lean_obj_tag(v_r_1719_) == 0)
{
lean_object* v_l_1806_; 
v_l_1806_ = lean_ctor_get(v_r_1719_, 3);
lean_inc(v_l_1806_);
if (lean_obj_tag(v_l_1806_) == 0)
{
lean_object* v_r_1807_; 
v_r_1807_ = lean_ctor_get(v_r_1719_, 4);
lean_inc(v_r_1807_);
if (lean_obj_tag(v_r_1807_) == 0)
{
lean_object* v_size_1808_; lean_object* v_k_1809_; lean_object* v_v_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1822_; 
v_size_1808_ = lean_ctor_get(v_r_1719_, 0);
v_k_1809_ = lean_ctor_get(v_r_1719_, 1);
v_v_1810_ = lean_ctor_get(v_r_1719_, 2);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_r_1719_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; lean_object* v_unused_1824_; 
v_unused_1823_ = lean_ctor_get(v_r_1719_, 4);
lean_dec(v_unused_1823_);
v_unused_1824_ = lean_ctor_get(v_r_1719_, 3);
lean_dec(v_unused_1824_);
v___x_1812_ = v_r_1719_;
v_isShared_1813_ = v_isSharedCheck_1822_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_v_1810_);
lean_inc(v_k_1809_);
lean_inc(v_size_1808_);
lean_dec(v_r_1719_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1822_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_size_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v_size_1814_ = lean_ctor_get(v_l_1806_, 0);
v___x_1815_ = lean_unsigned_to_nat(1u);
v___x_1816_ = lean_nat_add(v___x_1815_, v_size_1808_);
lean_dec(v_size_1808_);
v___x_1817_ = lean_nat_add(v___x_1815_, v_size_1814_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_l_1806_);
lean_ctor_set(v___x_1812_, 3, v_l_1718_);
lean_ctor_set(v___x_1812_, 2, v_v_1717_);
lean_ctor_set(v___x_1812_, 1, v_k_1716_);
lean_ctor_set(v___x_1812_, 0, v___x_1817_);
v___x_1819_ = v___x_1812_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_k_1716_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_v_1717_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_l_1718_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_l_1806_);
v___x_1819_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1816_);
lean_ctor_set(v___x_1820_, 1, v_k_1809_);
lean_ctor_set(v___x_1820_, 2, v_v_1810_);
lean_ctor_set(v___x_1820_, 3, v___x_1819_);
lean_ctor_set(v___x_1820_, 4, v_r_1807_);
return v___x_1820_;
}
}
}
else
{
lean_object* v_k_1825_; lean_object* v_v_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1848_; 
v_k_1825_ = lean_ctor_get(v_r_1719_, 1);
v_v_1826_ = lean_ctor_get(v_r_1719_, 2);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_r_1719_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; 
v_unused_1849_ = lean_ctor_get(v_r_1719_, 4);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_r_1719_, 3);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_r_1719_, 0);
lean_dec(v_unused_1851_);
v___x_1828_ = v_r_1719_;
v_isShared_1829_ = v_isSharedCheck_1848_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_v_1826_);
lean_inc(v_k_1825_);
lean_dec(v_r_1719_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1848_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_k_1830_; lean_object* v_v_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1844_; 
v_k_1830_ = lean_ctor_get(v_l_1806_, 1);
v_v_1831_ = lean_ctor_get(v_l_1806_, 2);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_l_1806_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; lean_object* v_unused_1846_; lean_object* v_unused_1847_; 
v_unused_1845_ = lean_ctor_get(v_l_1806_, 4);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v_l_1806_, 3);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v_l_1806_, 0);
lean_dec(v_unused_1847_);
v___x_1833_ = v_l_1806_;
v_isShared_1834_ = v_isSharedCheck_1844_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_v_1831_);
lean_inc(v_k_1830_);
lean_dec(v_l_1806_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1844_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1835_ = lean_unsigned_to_nat(3u);
v___x_1836_ = lean_unsigned_to_nat(1u);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 4, v_r_1807_);
lean_ctor_set(v___x_1833_, 3, v_r_1807_);
lean_ctor_set(v___x_1833_, 2, v_v_1717_);
lean_ctor_set(v___x_1833_, 1, v_k_1716_);
lean_ctor_set(v___x_1833_, 0, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_k_1716_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_v_1717_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_r_1807_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_r_1807_);
v___x_1838_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 3, v_r_1807_);
lean_ctor_set(v___x_1828_, 0, v___x_1836_);
v___x_1840_ = v___x_1828_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_k_1825_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_v_1826_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_r_1807_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_r_1807_);
v___x_1840_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1835_);
lean_ctor_set(v___x_1841_, 1, v_k_1830_);
lean_ctor_set(v___x_1841_, 2, v_v_1831_);
lean_ctor_set(v___x_1841_, 3, v___x_1838_);
lean_ctor_set(v___x_1841_, 4, v___x_1840_);
return v___x_1841_;
}
}
}
}
}
}
else
{
lean_object* v_r_1852_; 
v_r_1852_ = lean_ctor_get(v_r_1719_, 4);
lean_inc(v_r_1852_);
if (lean_obj_tag(v_r_1852_) == 0)
{
lean_object* v_k_1853_; lean_object* v_v_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1864_; 
v_k_1853_ = lean_ctor_get(v_r_1719_, 1);
v_v_1854_ = lean_ctor_get(v_r_1719_, 2);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_r_1719_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; 
v_unused_1865_ = lean_ctor_get(v_r_1719_, 4);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_r_1719_, 3);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_r_1719_, 0);
lean_dec(v_unused_1867_);
v___x_1856_ = v_r_1719_;
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_v_1854_);
lean_inc(v_k_1853_);
lean_dec(v_r_1719_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1858_ = lean_unsigned_to_nat(3u);
v___x_1859_ = lean_unsigned_to_nat(1u);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 4, v_l_1806_);
lean_ctor_set(v___x_1856_, 2, v_v_1717_);
lean_ctor_set(v___x_1856_, 1, v_k_1716_);
lean_ctor_set(v___x_1856_, 0, v___x_1859_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_k_1716_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_v_1717_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_l_1806_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_l_1806_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1858_);
lean_ctor_set(v___x_1862_, 1, v_k_1853_);
lean_ctor_set(v___x_1862_, 2, v_v_1854_);
lean_ctor_set(v___x_1862_, 3, v___x_1861_);
lean_ctor_set(v___x_1862_, 4, v_r_1852_);
return v___x_1862_;
}
}
}
else
{
lean_object* v_size_1868_; lean_object* v_k_1869_; lean_object* v_v_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1879_; 
v_size_1868_ = lean_ctor_get(v_r_1719_, 0);
v_k_1869_ = lean_ctor_get(v_r_1719_, 1);
v_v_1870_ = lean_ctor_get(v_r_1719_, 2);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_r_1719_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; lean_object* v_unused_1881_; 
v_unused_1880_ = lean_ctor_get(v_r_1719_, 4);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_r_1719_, 3);
lean_dec(v_unused_1881_);
v___x_1872_ = v_r_1719_;
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_v_1870_);
lean_inc(v_k_1869_);
lean_inc(v_size_1868_);
lean_dec(v_r_1719_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 3, v_r_1852_);
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_size_1868_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_k_1869_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_v_1870_);
lean_ctor_set(v_reuseFailAlloc_1878_, 3, v_r_1852_);
lean_ctor_set(v_reuseFailAlloc_1878_, 4, v_r_1852_);
v___x_1875_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_unsigned_to_nat(2u);
v___x_1877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v_k_1716_);
lean_ctor_set(v___x_1877_, 2, v_v_1717_);
lean_ctor_set(v___x_1877_, 3, v_r_1852_);
lean_ctor_set(v___x_1877_, 4, v___x_1875_);
return v___x_1877_;
}
}
}
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_k_1716_);
lean_ctor_set(v___x_1883_, 2, v_v_1717_);
lean_ctor_set(v___x_1883_, 3, v_r_1719_);
lean_ctor_set(v___x_1883_, 4, v_r_1719_);
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceRErase(lean_object* v_00_u03b1_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_k_1886_, lean_object* v_v_1887_, lean_object* v_l_1888_, lean_object* v_r_1889_, lean_object* v_hlb_1890_, lean_object* v_hrb_1891_, lean_object* v_hlr_1892_){
_start:
{
if (lean_obj_tag(v_l_1888_) == 0)
{
if (lean_obj_tag(v_r_1889_) == 0)
{
lean_object* v_size_1893_; lean_object* v_size_1894_; lean_object* v_k_1895_; lean_object* v_v_1896_; lean_object* v_l_1897_; lean_object* v_r_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v_size_1893_ = lean_ctor_get(v_l_1888_, 0);
v_size_1894_ = lean_ctor_get(v_r_1889_, 0);
v_k_1895_ = lean_ctor_get(v_r_1889_, 1);
v_v_1896_ = lean_ctor_get(v_r_1889_, 2);
v_l_1897_ = lean_ctor_get(v_r_1889_, 3);
lean_inc(v_l_1897_);
v_r_1898_ = lean_ctor_get(v_r_1889_, 4);
v___x_1899_ = lean_unsigned_to_nat(3u);
v___x_1900_ = lean_nat_mul(v___x_1899_, v_size_1893_);
v___x_1901_ = lean_nat_dec_lt(v___x_1900_, v_size_1894_);
lean_dec(v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec(v_l_1897_);
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_add(v___x_1902_, v_size_1893_);
v___x_1904_ = lean_nat_add(v___x_1903_, v_size_1894_);
lean_dec(v___x_1903_);
v___x_1905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v_k_1886_);
lean_ctor_set(v___x_1905_, 2, v_v_1887_);
lean_ctor_set(v___x_1905_, 3, v_l_1888_);
lean_ctor_set(v___x_1905_, 4, v_r_1889_);
return v___x_1905_;
}
else
{
lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1969_; 
lean_inc(v_r_1898_);
lean_inc(v_v_1896_);
lean_inc(v_k_1895_);
lean_inc(v_size_1894_);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_r_1889_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; lean_object* v_unused_1971_; lean_object* v_unused_1972_; lean_object* v_unused_1973_; lean_object* v_unused_1974_; 
v_unused_1970_ = lean_ctor_get(v_r_1889_, 4);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_r_1889_, 3);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_r_1889_, 2);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v_r_1889_, 1);
lean_dec(v_unused_1973_);
v_unused_1974_ = lean_ctor_get(v_r_1889_, 0);
lean_dec(v_unused_1974_);
v___x_1907_ = v_r_1889_;
v_isShared_1908_ = v_isSharedCheck_1969_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v_r_1889_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1969_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_size_1909_; lean_object* v_k_1910_; lean_object* v_v_1911_; lean_object* v_l_1912_; lean_object* v_r_1913_; lean_object* v_size_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_size_1909_ = lean_ctor_get(v_l_1897_, 0);
v_k_1910_ = lean_ctor_get(v_l_1897_, 1);
v_v_1911_ = lean_ctor_get(v_l_1897_, 2);
v_l_1912_ = lean_ctor_get(v_l_1897_, 3);
v_r_1913_ = lean_ctor_get(v_l_1897_, 4);
v_size_1914_ = lean_ctor_get(v_r_1898_, 0);
v___x_1915_ = lean_unsigned_to_nat(2u);
v___x_1916_ = lean_nat_mul(v___x_1915_, v_size_1914_);
v___x_1917_ = lean_nat_dec_lt(v_size_1909_, v___x_1916_);
lean_dec(v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1944_; 
lean_inc(v_r_1913_);
lean_inc(v_l_1912_);
lean_inc(v_v_1911_);
lean_inc(v_k_1910_);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_l_1897_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; lean_object* v_unused_1946_; lean_object* v_unused_1947_; lean_object* v_unused_1948_; lean_object* v_unused_1949_; 
v_unused_1945_ = lean_ctor_get(v_l_1897_, 4);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_l_1897_, 3);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_l_1897_, 2);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_l_1897_, 1);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_l_1897_, 0);
lean_dec(v_unused_1949_);
v___x_1919_ = v_l_1897_;
v_isShared_1920_ = v_isSharedCheck_1944_;
goto v_resetjp_1918_;
}
else
{
lean_dec(v_l_1897_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1944_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1936_; 
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = lean_nat_add(v___x_1921_, v_size_1893_);
v___x_1923_ = lean_nat_add(v___x_1922_, v_size_1894_);
lean_dec(v_size_1894_);
if (lean_obj_tag(v_l_1912_) == 0)
{
lean_object* v_size_1942_; 
v_size_1942_ = lean_ctor_get(v_l_1912_, 0);
lean_inc(v_size_1942_);
v___y_1936_ = v_size_1942_;
goto v___jp_1935_;
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_unsigned_to_nat(0u);
v___y_1936_ = v___x_1943_;
goto v___jp_1935_;
}
v___jp_1924_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_nat_add(v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 4, v_r_1898_);
lean_ctor_set(v___x_1919_, 3, v_r_1913_);
lean_ctor_set(v___x_1919_, 2, v_v_1896_);
lean_ctor_set(v___x_1919_, 1, v_k_1895_);
lean_ctor_set(v___x_1919_, 0, v___x_1928_);
v___x_1930_ = v___x_1919_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_k_1895_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_v_1896_);
lean_ctor_set(v_reuseFailAlloc_1934_, 3, v_r_1913_);
lean_ctor_set(v_reuseFailAlloc_1934_, 4, v_r_1898_);
v___x_1930_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1932_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 4, v___x_1930_);
lean_ctor_set(v___x_1907_, 3, v___y_1925_);
lean_ctor_set(v___x_1907_, 2, v_v_1911_);
lean_ctor_set(v___x_1907_, 1, v_k_1910_);
lean_ctor_set(v___x_1907_, 0, v___x_1923_);
v___x_1932_ = v___x_1907_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_k_1910_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_v_1911_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v___y_1925_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
v___jp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = lean_nat_add(v___x_1922_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec(v___x_1922_);
v___x_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v_k_1886_);
lean_ctor_set(v___x_1938_, 2, v_v_1887_);
lean_ctor_set(v___x_1938_, 3, v_l_1888_);
lean_ctor_set(v___x_1938_, 4, v_l_1912_);
v___x_1939_ = lean_nat_add(v___x_1921_, v_size_1914_);
if (lean_obj_tag(v_r_1913_) == 0)
{
lean_object* v_size_1940_; 
v_size_1940_ = lean_ctor_get(v_r_1913_, 0);
lean_inc(v_size_1940_);
v___y_1925_ = v___x_1938_;
v___y_1926_ = v___x_1939_;
v___y_1927_ = v_size_1940_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___y_1925_ = v___x_1938_;
v___y_1926_ = v___x_1939_;
v___y_1927_ = v___x_1941_;
goto v___jp_1924_;
}
}
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = lean_nat_add(v___x_1950_, v_size_1893_);
v___x_1952_ = lean_nat_add(v___x_1951_, v_size_1894_);
lean_dec(v_size_1894_);
v___x_1953_ = lean_nat_add(v___x_1951_, v_size_1909_);
lean_dec(v___x_1951_);
lean_inc_ref(v_l_1888_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 4, v_l_1897_);
lean_ctor_set(v___x_1907_, 3, v_l_1888_);
lean_ctor_set(v___x_1907_, 2, v_v_1887_);
lean_ctor_set(v___x_1907_, 1, v_k_1886_);
lean_ctor_set(v___x_1907_, 0, v___x_1953_);
v___x_1955_ = v___x_1907_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_l_1888_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v_l_1897_);
v___x_1955_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_isSharedCheck_1962_ = !lean_is_exclusive(v_l_1888_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; lean_object* v_unused_1964_; lean_object* v_unused_1965_; lean_object* v_unused_1966_; lean_object* v_unused_1967_; 
v_unused_1963_ = lean_ctor_get(v_l_1888_, 4);
lean_dec(v_unused_1963_);
v_unused_1964_ = lean_ctor_get(v_l_1888_, 3);
lean_dec(v_unused_1964_);
v_unused_1965_ = lean_ctor_get(v_l_1888_, 2);
lean_dec(v_unused_1965_);
v_unused_1966_ = lean_ctor_get(v_l_1888_, 1);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_l_1888_, 0);
lean_dec(v_unused_1967_);
v___x_1957_ = v_l_1888_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_dec(v_l_1888_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 4, v_r_1898_);
lean_ctor_set(v___x_1957_, 3, v___x_1955_);
lean_ctor_set(v___x_1957_, 2, v_v_1896_);
lean_ctor_set(v___x_1957_, 1, v_k_1895_);
lean_ctor_set(v___x_1957_, 0, v___x_1952_);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_k_1895_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_v_1896_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_r_1898_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_size_1975_ = lean_ctor_get(v_l_1888_, 0);
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_add(v___x_1976_, v_size_1975_);
v___x_1978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v_k_1886_);
lean_ctor_set(v___x_1978_, 2, v_v_1887_);
lean_ctor_set(v___x_1978_, 3, v_l_1888_);
lean_ctor_set(v___x_1978_, 4, v_r_1889_);
return v___x_1978_;
}
}
else
{
if (lean_obj_tag(v_r_1889_) == 0)
{
lean_object* v_l_1979_; 
v_l_1979_ = lean_ctor_get(v_r_1889_, 3);
lean_inc(v_l_1979_);
if (lean_obj_tag(v_l_1979_) == 0)
{
lean_object* v_r_1980_; 
v_r_1980_ = lean_ctor_get(v_r_1889_, 4);
lean_inc(v_r_1980_);
if (lean_obj_tag(v_r_1980_) == 0)
{
lean_object* v_size_1981_; lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1995_; 
v_size_1981_ = lean_ctor_get(v_r_1889_, 0);
v_k_1982_ = lean_ctor_get(v_r_1889_, 1);
v_v_1983_ = lean_ctor_get(v_r_1889_, 2);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_r_1889_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; 
v_unused_1996_ = lean_ctor_get(v_r_1889_, 4);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_r_1889_, 3);
lean_dec(v_unused_1997_);
v___x_1985_ = v_r_1889_;
v_isShared_1986_ = v_isSharedCheck_1995_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
lean_inc(v_size_1981_);
lean_dec(v_r_1889_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1995_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_size_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v_size_1987_ = lean_ctor_get(v_l_1979_, 0);
v___x_1988_ = lean_unsigned_to_nat(1u);
v___x_1989_ = lean_nat_add(v___x_1988_, v_size_1981_);
lean_dec(v_size_1981_);
v___x_1990_ = lean_nat_add(v___x_1988_, v_size_1987_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 4, v_l_1979_);
lean_ctor_set(v___x_1985_, 3, v_l_1888_);
lean_ctor_set(v___x_1985_, 2, v_v_1887_);
lean_ctor_set(v___x_1985_, 1, v_k_1886_);
lean_ctor_set(v___x_1985_, 0, v___x_1990_);
v___x_1992_ = v___x_1985_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_l_1888_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_l_1979_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1989_);
lean_ctor_set(v___x_1993_, 1, v_k_1982_);
lean_ctor_set(v___x_1993_, 2, v_v_1983_);
lean_ctor_set(v___x_1993_, 3, v___x_1992_);
lean_ctor_set(v___x_1993_, 4, v_r_1980_);
return v___x_1993_;
}
}
}
else
{
lean_object* v_k_1998_; lean_object* v_v_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2021_; 
v_k_1998_ = lean_ctor_get(v_r_1889_, 1);
v_v_1999_ = lean_ctor_get(v_r_1889_, 2);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_r_1889_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; lean_object* v_unused_2023_; lean_object* v_unused_2024_; 
v_unused_2022_ = lean_ctor_get(v_r_1889_, 4);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_r_1889_, 3);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_r_1889_, 0);
lean_dec(v_unused_2024_);
v___x_2001_ = v_r_1889_;
v_isShared_2002_ = v_isSharedCheck_2021_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_v_1999_);
lean_inc(v_k_1998_);
lean_dec(v_r_1889_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2021_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_k_2003_; lean_object* v_v_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2017_; 
v_k_2003_ = lean_ctor_get(v_l_1979_, 1);
v_v_2004_ = lean_ctor_get(v_l_1979_, 2);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_l_1979_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; lean_object* v_unused_2019_; lean_object* v_unused_2020_; 
v_unused_2018_ = lean_ctor_get(v_l_1979_, 4);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_l_1979_, 3);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_l_1979_, 0);
lean_dec(v_unused_2020_);
v___x_2006_ = v_l_1979_;
v_isShared_2007_ = v_isSharedCheck_2017_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_v_2004_);
lean_inc(v_k_2003_);
lean_dec(v_l_1979_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2017_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2008_ = lean_unsigned_to_nat(3u);
v___x_2009_ = lean_unsigned_to_nat(1u);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 4, v_r_1980_);
lean_ctor_set(v___x_2006_, 3, v_r_1980_);
lean_ctor_set(v___x_2006_, 2, v_v_1887_);
lean_ctor_set(v___x_2006_, 1, v_k_1886_);
lean_ctor_set(v___x_2006_, 0, v___x_2009_);
v___x_2011_ = v___x_2006_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_r_1980_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_r_1980_);
v___x_2011_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2013_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 3, v_r_1980_);
lean_ctor_set(v___x_2001_, 0, v___x_2009_);
v___x_2013_ = v___x_2001_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_k_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_v_1999_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_r_1980_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_r_1980_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2008_);
lean_ctor_set(v___x_2014_, 1, v_k_2003_);
lean_ctor_set(v___x_2014_, 2, v_v_2004_);
lean_ctor_set(v___x_2014_, 3, v___x_2011_);
lean_ctor_set(v___x_2014_, 4, v___x_2013_);
return v___x_2014_;
}
}
}
}
}
}
else
{
lean_object* v_r_2025_; 
v_r_2025_ = lean_ctor_get(v_r_1889_, 4);
lean_inc(v_r_2025_);
if (lean_obj_tag(v_r_2025_) == 0)
{
lean_object* v_k_2026_; lean_object* v_v_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2037_; 
v_k_2026_ = lean_ctor_get(v_r_1889_, 1);
v_v_2027_ = lean_ctor_get(v_r_1889_, 2);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_r_1889_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2038_ = lean_ctor_get(v_r_1889_, 4);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_r_1889_, 3);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_r_1889_, 0);
lean_dec(v_unused_2040_);
v___x_2029_ = v_r_1889_;
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_v_2027_);
lean_inc(v_k_2026_);
lean_dec(v_r_1889_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2031_ = lean_unsigned_to_nat(3u);
v___x_2032_ = lean_unsigned_to_nat(1u);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_l_1979_);
lean_ctor_set(v___x_2029_, 2, v_v_1887_);
lean_ctor_set(v___x_2029_, 1, v_k_1886_);
lean_ctor_set(v___x_2029_, 0, v___x_2032_);
v___x_2034_ = v___x_2029_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_l_1979_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_l_1979_);
v___x_2034_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2031_);
lean_ctor_set(v___x_2035_, 1, v_k_2026_);
lean_ctor_set(v___x_2035_, 2, v_v_2027_);
lean_ctor_set(v___x_2035_, 3, v___x_2034_);
lean_ctor_set(v___x_2035_, 4, v_r_2025_);
return v___x_2035_;
}
}
}
else
{
lean_object* v_size_2041_; lean_object* v_k_2042_; lean_object* v_v_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2052_; 
v_size_2041_ = lean_ctor_get(v_r_1889_, 0);
v_k_2042_ = lean_ctor_get(v_r_1889_, 1);
v_v_2043_ = lean_ctor_get(v_r_1889_, 2);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_r_1889_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; lean_object* v_unused_2054_; 
v_unused_2053_ = lean_ctor_get(v_r_1889_, 4);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_r_1889_, 3);
lean_dec(v_unused_2054_);
v___x_2045_ = v_r_1889_;
v_isShared_2046_ = v_isSharedCheck_2052_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_v_2043_);
lean_inc(v_k_2042_);
lean_inc(v_size_2041_);
lean_dec(v_r_1889_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2052_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 3, v_r_2025_);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_size_2041_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_k_2042_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_v_2043_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_r_2025_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_r_2025_);
v___x_2048_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_unsigned_to_nat(2u);
v___x_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_k_1886_);
lean_ctor_set(v___x_2050_, 2, v_v_1887_);
lean_ctor_set(v___x_2050_, 3, v_r_2025_);
lean_ctor_set(v___x_2050_, 4, v___x_2048_);
return v___x_2050_;
}
}
}
}
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v_k_1886_);
lean_ctor_set(v___x_2056_, 2, v_v_1887_);
lean_ctor_set(v___x_2056_, 3, v_r_1889_);
lean_ctor_set(v___x_2056_, 4, v_r_1889_);
return v___x_2056_;
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2059_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
v___x_2060_ = lean_unsigned_to_nat(35u);
v___x_2061_ = lean_unsigned_to_nat(276u);
v___x_2062_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
v___x_2063_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2064_ = l_mkPanicMessageWithDecl(v___x_2063_, v___x_2062_, v___x_2061_, v___x_2060_, v___x_2059_);
return v___x_2064_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2065_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__1));
v___x_2066_ = lean_unsigned_to_nat(21u);
v___x_2067_ = lean_unsigned_to_nat(277u);
v___x_2068_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__0));
v___x_2069_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_balanceL_x21___redArg___closed__0));
v___x_2070_ = l_mkPanicMessageWithDecl(v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_, v___x_2065_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg(lean_object* v_k_2071_, lean_object* v_v_2072_, lean_object* v_l_2073_, lean_object* v_r_2074_){
_start:
{
if (lean_obj_tag(v_l_2073_) == 0)
{
if (lean_obj_tag(v_r_2074_) == 0)
{
lean_object* v_size_2075_; lean_object* v_size_2076_; lean_object* v_k_2077_; lean_object* v_v_2078_; lean_object* v_l_2079_; lean_object* v_r_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v_size_2075_ = lean_ctor_get(v_l_2073_, 0);
v_size_2076_ = lean_ctor_get(v_r_2074_, 0);
v_k_2077_ = lean_ctor_get(v_r_2074_, 1);
v_v_2078_ = lean_ctor_get(v_r_2074_, 2);
v_l_2079_ = lean_ctor_get(v_r_2074_, 3);
lean_inc(v_l_2079_);
v_r_2080_ = lean_ctor_get(v_r_2074_, 4);
v___x_2081_ = lean_unsigned_to_nat(3u);
v___x_2082_ = lean_nat_mul(v___x_2081_, v_size_2075_);
v___x_2083_ = lean_nat_dec_lt(v___x_2082_, v_size_2076_);
lean_dec(v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v_l_2079_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_add(v___x_2084_, v_size_2075_);
v___x_2086_ = lean_nat_add(v___x_2085_, v_size_2076_);
lean_dec(v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v_k_2071_);
lean_ctor_set(v___x_2087_, 2, v_v_2072_);
lean_ctor_set(v___x_2087_, 3, v_l_2073_);
lean_ctor_set(v___x_2087_, 4, v_r_2074_);
return v___x_2087_;
}
else
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2156_; 
lean_inc(v_r_2080_);
lean_inc(v_v_2078_);
lean_inc(v_k_2077_);
lean_inc(v_size_2076_);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_r_2074_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2157_ = lean_ctor_get(v_r_2074_, 4);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_r_2074_, 3);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_r_2074_, 2);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_r_2074_, 1);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_r_2074_, 0);
lean_dec(v_unused_2161_);
v___x_2089_ = v_r_2074_;
v_isShared_2090_ = v_isSharedCheck_2156_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v_r_2074_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2156_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_box(1);
if (lean_obj_tag(v_l_2079_) == 0)
{
if (lean_obj_tag(v_r_2080_) == 0)
{
lean_object* v_size_2092_; lean_object* v_k_2093_; lean_object* v_v_2094_; lean_object* v_l_2095_; lean_object* v_r_2096_; lean_object* v_size_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_size_2092_ = lean_ctor_get(v_l_2079_, 0);
v_k_2093_ = lean_ctor_get(v_l_2079_, 1);
v_v_2094_ = lean_ctor_get(v_l_2079_, 2);
v_l_2095_ = lean_ctor_get(v_l_2079_, 3);
v_r_2096_ = lean_ctor_get(v_l_2079_, 4);
v_size_2097_ = lean_ctor_get(v_r_2080_, 0);
v___x_2098_ = lean_unsigned_to_nat(2u);
v___x_2099_ = lean_nat_mul(v___x_2098_, v_size_2097_);
v___x_2100_ = lean_nat_dec_lt(v_size_2092_, v___x_2099_);
lean_dec(v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2127_; 
lean_inc(v_r_2096_);
lean_inc(v_l_2095_);
lean_inc(v_v_2094_);
lean_inc(v_k_2093_);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_l_2079_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2128_ = lean_ctor_get(v_l_2079_, 4);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_l_2079_, 3);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_l_2079_, 2);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_l_2079_, 1);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_2079_, 0);
lean_dec(v_unused_2132_);
v___x_2102_ = v_l_2079_;
v_isShared_2103_ = v_isSharedCheck_2127_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_l_2079_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2127_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2119_; 
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_add(v___x_2104_, v_size_2075_);
v___x_2106_ = lean_nat_add(v___x_2105_, v_size_2076_);
lean_dec(v_size_2076_);
if (lean_obj_tag(v_l_2095_) == 0)
{
lean_object* v_size_2125_; 
v_size_2125_ = lean_ctor_get(v_l_2095_, 0);
lean_inc(v_size_2125_);
v___y_2119_ = v_size_2125_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___y_2119_ = v___x_2126_;
goto v___jp_2118_;
}
v___jp_2107_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_nat_add(v___y_2108_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec(v___y_2108_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v_r_2080_);
lean_ctor_set(v___x_2102_, 3, v_r_2096_);
lean_ctor_set(v___x_2102_, 2, v_v_2078_);
lean_ctor_set(v___x_2102_, 1, v_k_2077_);
lean_ctor_set(v___x_2102_, 0, v___x_2111_);
v___x_2113_ = v___x_2102_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_r_2096_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_r_2080_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v___x_2113_);
lean_ctor_set(v___x_2089_, 3, v___y_2109_);
lean_ctor_set(v___x_2089_, 2, v_v_2094_);
lean_ctor_set(v___x_2089_, 1, v_k_2093_);
lean_ctor_set(v___x_2089_, 0, v___x_2106_);
v___x_2115_ = v___x_2089_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2093_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2094_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v___y_2109_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = lean_nat_add(v___x_2105_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec(v___x_2105_);
v___x_2121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v_k_2071_);
lean_ctor_set(v___x_2121_, 2, v_v_2072_);
lean_ctor_set(v___x_2121_, 3, v_l_2073_);
lean_ctor_set(v___x_2121_, 4, v_l_2095_);
v___x_2122_ = lean_nat_add(v___x_2104_, v_size_2097_);
if (lean_obj_tag(v_r_2096_) == 0)
{
lean_object* v_size_2123_; 
v_size_2123_ = lean_ctor_get(v_r_2096_, 0);
lean_inc(v_size_2123_);
v___y_2108_ = v___x_2122_;
v___y_2109_ = v___x_2121_;
v___y_2110_ = v_size_2123_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v___y_2108_ = v___x_2122_;
v___y_2109_ = v___x_2121_;
v___y_2110_ = v___x_2124_;
goto v___jp_2107_;
}
}
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_add(v___x_2133_, v_size_2075_);
v___x_2135_ = lean_nat_add(v___x_2134_, v_size_2076_);
lean_dec(v_size_2076_);
v___x_2136_ = lean_nat_add(v___x_2134_, v_size_2092_);
lean_dec(v___x_2134_);
lean_inc_ref(v_l_2073_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_l_2079_);
lean_ctor_set(v___x_2089_, 3, v_l_2073_);
lean_ctor_set(v___x_2089_, 2, v_v_2072_);
lean_ctor_set(v___x_2089_, 1, v_k_2071_);
lean_ctor_set(v___x_2089_, 0, v___x_2136_);
v___x_2138_ = v___x_2089_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_k_2071_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_v_2072_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v_l_2073_);
lean_ctor_set(v_reuseFailAlloc_2151_, 4, v_l_2079_);
v___x_2138_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_isSharedCheck_2145_ = !lean_is_exclusive(v_l_2073_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; 
v_unused_2146_ = lean_ctor_get(v_l_2073_, 4);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_l_2073_, 3);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2073_, 2);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2073_, 1);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2073_, 0);
lean_dec(v_unused_2150_);
v___x_2140_ = v_l_2073_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v_l_2073_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 4, v_r_2080_);
lean_ctor_set(v___x_2140_, 3, v___x_2138_);
lean_ctor_set(v___x_2140_, 2, v_v_2078_);
lean_ctor_set(v___x_2140_, 1, v_k_2077_);
lean_ctor_set(v___x_2140_, 0, v___x_2135_);
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_r_2080_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref_known(v_l_2079_, 5);
lean_del_object(v___x_2089_);
lean_dec(v_v_2078_);
lean_dec(v_k_2077_);
lean_dec(v_size_2076_);
lean_dec_ref_known(v_l_2073_, 5);
lean_dec(v_v_2072_);
lean_dec(v_k_2071_);
v___x_2152_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
v___x_2153_ = l_panic___redArg(v___x_2091_, v___x_2152_);
return v___x_2153_;
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_del_object(v___x_2089_);
lean_dec(v_r_2080_);
lean_dec(v_v_2078_);
lean_dec(v_k_2077_);
lean_dec(v_size_2076_);
lean_dec_ref_known(v_l_2073_, 5);
lean_dec(v_v_2072_);
lean_dec(v_k_2071_);
v___x_2154_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
v___x_2155_ = l_panic___redArg(v___x_2091_, v___x_2154_);
return v___x_2155_;
}
}
}
}
else
{
lean_object* v_size_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_size_2162_ = lean_ctor_get(v_l_2073_, 0);
v___x_2163_ = lean_unsigned_to_nat(1u);
v___x_2164_ = lean_nat_add(v___x_2163_, v_size_2162_);
v___x_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v_k_2071_);
lean_ctor_set(v___x_2165_, 2, v_v_2072_);
lean_ctor_set(v___x_2165_, 3, v_l_2073_);
lean_ctor_set(v___x_2165_, 4, v_r_2074_);
return v___x_2165_;
}
}
else
{
if (lean_obj_tag(v_r_2074_) == 0)
{
lean_object* v_l_2166_; 
v_l_2166_ = lean_ctor_get(v_r_2074_, 3);
lean_inc(v_l_2166_);
if (lean_obj_tag(v_l_2166_) == 0)
{
lean_object* v_r_2167_; 
v_r_2167_ = lean_ctor_get(v_r_2074_, 4);
lean_inc(v_r_2167_);
if (lean_obj_tag(v_r_2167_) == 0)
{
lean_object* v_size_2168_; lean_object* v_k_2169_; lean_object* v_v_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2182_; 
v_size_2168_ = lean_ctor_get(v_r_2074_, 0);
v_k_2169_ = lean_ctor_get(v_r_2074_, 1);
v_v_2170_ = lean_ctor_get(v_r_2074_, 2);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_r_2074_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2183_ = lean_ctor_get(v_r_2074_, 4);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_r_2074_, 3);
lean_dec(v_unused_2184_);
v___x_2172_ = v_r_2074_;
v_isShared_2173_ = v_isSharedCheck_2182_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_v_2170_);
lean_inc(v_k_2169_);
lean_inc(v_size_2168_);
lean_dec(v_r_2074_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2182_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_size_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
v_size_2174_ = lean_ctor_get(v_l_2166_, 0);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_add(v___x_2175_, v_size_2168_);
lean_dec(v_size_2168_);
v___x_2177_ = lean_nat_add(v___x_2175_, v_size_2174_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 4, v_l_2166_);
lean_ctor_set(v___x_2172_, 3, v_l_2073_);
lean_ctor_set(v___x_2172_, 2, v_v_2072_);
lean_ctor_set(v___x_2172_, 1, v_k_2071_);
lean_ctor_set(v___x_2172_, 0, v___x_2177_);
v___x_2179_ = v___x_2172_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2071_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2072_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_l_2073_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_l_2166_);
v___x_2179_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2176_);
lean_ctor_set(v___x_2180_, 1, v_k_2169_);
lean_ctor_set(v___x_2180_, 2, v_v_2170_);
lean_ctor_set(v___x_2180_, 3, v___x_2179_);
lean_ctor_set(v___x_2180_, 4, v_r_2167_);
return v___x_2180_;
}
}
}
else
{
lean_object* v_k_2185_; lean_object* v_v_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2208_; 
v_k_2185_ = lean_ctor_get(v_r_2074_, 1);
v_v_2186_ = lean_ctor_get(v_r_2074_, 2);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_r_2074_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; 
v_unused_2209_ = lean_ctor_get(v_r_2074_, 4);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_r_2074_, 3);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_r_2074_, 0);
lean_dec(v_unused_2211_);
v___x_2188_ = v_r_2074_;
v_isShared_2189_ = v_isSharedCheck_2208_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_v_2186_);
lean_inc(v_k_2185_);
lean_dec(v_r_2074_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2208_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_k_2190_; lean_object* v_v_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2204_; 
v_k_2190_ = lean_ctor_get(v_l_2166_, 1);
v_v_2191_ = lean_ctor_get(v_l_2166_, 2);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_l_2166_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; 
v_unused_2205_ = lean_ctor_get(v_l_2166_, 4);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_l_2166_, 3);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_l_2166_, 0);
lean_dec(v_unused_2207_);
v___x_2193_ = v_l_2166_;
v_isShared_2194_ = v_isSharedCheck_2204_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_v_2191_);
lean_inc(v_k_2190_);
lean_dec(v_l_2166_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2204_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2195_ = lean_unsigned_to_nat(3u);
v___x_2196_ = lean_unsigned_to_nat(1u);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 4, v_r_2167_);
lean_ctor_set(v___x_2193_, 3, v_r_2167_);
lean_ctor_set(v___x_2193_, 2, v_v_2072_);
lean_ctor_set(v___x_2193_, 1, v_k_2071_);
lean_ctor_set(v___x_2193_, 0, v___x_2196_);
v___x_2198_ = v___x_2193_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_k_2071_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_v_2072_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_r_2167_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v_r_2167_);
v___x_2198_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2200_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 3, v_r_2167_);
lean_ctor_set(v___x_2188_, 0, v___x_2196_);
v___x_2200_ = v___x_2188_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_k_2185_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_v_2186_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_r_2167_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_r_2167_);
v___x_2200_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2195_);
lean_ctor_set(v___x_2201_, 1, v_k_2190_);
lean_ctor_set(v___x_2201_, 2, v_v_2191_);
lean_ctor_set(v___x_2201_, 3, v___x_2198_);
lean_ctor_set(v___x_2201_, 4, v___x_2200_);
return v___x_2201_;
}
}
}
}
}
}
else
{
lean_object* v_r_2212_; 
v_r_2212_ = lean_ctor_get(v_r_2074_, 4);
lean_inc(v_r_2212_);
if (lean_obj_tag(v_r_2212_) == 0)
{
lean_object* v_k_2213_; lean_object* v_v_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2224_; 
v_k_2213_ = lean_ctor_get(v_r_2074_, 1);
v_v_2214_ = lean_ctor_get(v_r_2074_, 2);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_r_2074_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2225_ = lean_ctor_get(v_r_2074_, 4);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_r_2074_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_r_2074_, 0);
lean_dec(v_unused_2227_);
v___x_2216_ = v_r_2074_;
v_isShared_2217_ = v_isSharedCheck_2224_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_v_2214_);
lean_inc(v_k_2213_);
lean_dec(v_r_2074_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2224_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2218_ = lean_unsigned_to_nat(3u);
v___x_2219_ = lean_unsigned_to_nat(1u);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 4, v_l_2166_);
lean_ctor_set(v___x_2216_, 2, v_v_2072_);
lean_ctor_set(v___x_2216_, 1, v_k_2071_);
lean_ctor_set(v___x_2216_, 0, v___x_2219_);
v___x_2221_ = v___x_2216_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2071_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2072_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_l_2166_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_l_2166_);
v___x_2221_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2218_);
lean_ctor_set(v___x_2222_, 1, v_k_2213_);
lean_ctor_set(v___x_2222_, 2, v_v_2214_);
lean_ctor_set(v___x_2222_, 3, v___x_2221_);
lean_ctor_set(v___x_2222_, 4, v_r_2212_);
return v___x_2222_;
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_unsigned_to_nat(2u);
v___x_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v_k_2071_);
lean_ctor_set(v___x_2229_, 2, v_v_2072_);
lean_ctor_set(v___x_2229_, 3, v_r_2212_);
lean_ctor_set(v___x_2229_, 4, v_r_2074_);
return v___x_2229_;
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v_k_2071_);
lean_ctor_set(v___x_2231_, 2, v_v_2072_);
lean_ctor_set(v___x_2231_, 3, v_r_2074_);
lean_ctor_set(v___x_2231_, 4, v_r_2074_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_balanceR_x21(lean_object* v_00_u03b1_2232_, lean_object* v_00_u03b2_2233_, lean_object* v_k_2234_, lean_object* v_v_2235_, lean_object* v_l_2236_, lean_object* v_r_2237_){
_start:
{
if (lean_obj_tag(v_l_2236_) == 0)
{
if (lean_obj_tag(v_r_2237_) == 0)
{
lean_object* v_size_2238_; lean_object* v_size_2239_; lean_object* v_k_2240_; lean_object* v_v_2241_; lean_object* v_l_2242_; lean_object* v_r_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_size_2238_ = lean_ctor_get(v_l_2236_, 0);
v_size_2239_ = lean_ctor_get(v_r_2237_, 0);
v_k_2240_ = lean_ctor_get(v_r_2237_, 1);
v_v_2241_ = lean_ctor_get(v_r_2237_, 2);
v_l_2242_ = lean_ctor_get(v_r_2237_, 3);
lean_inc(v_l_2242_);
v_r_2243_ = lean_ctor_get(v_r_2237_, 4);
v___x_2244_ = lean_unsigned_to_nat(3u);
v___x_2245_ = lean_nat_mul(v___x_2244_, v_size_2238_);
v___x_2246_ = lean_nat_dec_lt(v___x_2245_, v_size_2239_);
lean_dec(v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec(v_l_2242_);
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_nat_add(v___x_2247_, v_size_2238_);
v___x_2249_ = lean_nat_add(v___x_2248_, v_size_2239_);
lean_dec(v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_k_2234_);
lean_ctor_set(v___x_2250_, 2, v_v_2235_);
lean_ctor_set(v___x_2250_, 3, v_l_2236_);
lean_ctor_set(v___x_2250_, 4, v_r_2237_);
return v___x_2250_;
}
else
{
lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2319_; 
lean_inc(v_r_2243_);
lean_inc(v_v_2241_);
lean_inc(v_k_2240_);
lean_inc(v_size_2239_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_r_2237_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2320_ = lean_ctor_get(v_r_2237_, 4);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_r_2237_, 3);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_r_2237_, 2);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_r_2237_, 1);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_r_2237_, 0);
lean_dec(v_unused_2324_);
v___x_2252_ = v_r_2237_;
v_isShared_2253_ = v_isSharedCheck_2319_;
goto v_resetjp_2251_;
}
else
{
lean_dec(v_r_2237_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2319_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_box(1);
if (lean_obj_tag(v_l_2242_) == 0)
{
if (lean_obj_tag(v_r_2243_) == 0)
{
lean_object* v_size_2255_; lean_object* v_k_2256_; lean_object* v_v_2257_; lean_object* v_l_2258_; lean_object* v_r_2259_; lean_object* v_size_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_size_2255_ = lean_ctor_get(v_l_2242_, 0);
v_k_2256_ = lean_ctor_get(v_l_2242_, 1);
v_v_2257_ = lean_ctor_get(v_l_2242_, 2);
v_l_2258_ = lean_ctor_get(v_l_2242_, 3);
v_r_2259_ = lean_ctor_get(v_l_2242_, 4);
v_size_2260_ = lean_ctor_get(v_r_2243_, 0);
v___x_2261_ = lean_unsigned_to_nat(2u);
v___x_2262_ = lean_nat_mul(v___x_2261_, v_size_2260_);
v___x_2263_ = lean_nat_dec_lt(v_size_2255_, v___x_2262_);
lean_dec(v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2290_; 
lean_inc(v_r_2259_);
lean_inc(v_l_2258_);
lean_inc(v_v_2257_);
lean_inc(v_k_2256_);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; lean_object* v_unused_2292_; lean_object* v_unused_2293_; lean_object* v_unused_2294_; lean_object* v_unused_2295_; 
v_unused_2291_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_l_2242_, 2);
lean_dec(v_unused_2293_);
v_unused_2294_ = lean_ctor_get(v_l_2242_, 1);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2295_);
v___x_2265_ = v_l_2242_;
v_isShared_2266_ = v_isSharedCheck_2290_;
goto v_resetjp_2264_;
}
else
{
lean_dec(v_l_2242_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2290_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2282_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_nat_add(v___x_2267_, v_size_2238_);
v___x_2269_ = lean_nat_add(v___x_2268_, v_size_2239_);
lean_dec(v_size_2239_);
if (lean_obj_tag(v_l_2258_) == 0)
{
lean_object* v_size_2288_; 
v_size_2288_ = lean_ctor_get(v_l_2258_, 0);
lean_inc(v_size_2288_);
v___y_2282_ = v_size_2288_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_unsigned_to_nat(0u);
v___y_2282_ = v___x_2289_;
goto v___jp_2281_;
}
v___jp_2270_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_nat_add(v___y_2271_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec(v___y_2271_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 4, v_r_2243_);
lean_ctor_set(v___x_2265_, 3, v_r_2259_);
lean_ctor_set(v___x_2265_, 2, v_v_2241_);
lean_ctor_set(v___x_2265_, 1, v_k_2240_);
lean_ctor_set(v___x_2265_, 0, v___x_2274_);
v___x_2276_ = v___x_2265_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_r_2259_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_r_2243_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 4, v___x_2276_);
lean_ctor_set(v___x_2252_, 3, v___y_2272_);
lean_ctor_set(v___x_2252_, 2, v_v_2257_);
lean_ctor_set(v___x_2252_, 1, v_k_2256_);
lean_ctor_set(v___x_2252_, 0, v___x_2269_);
v___x_2278_ = v___x_2252_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v___y_2272_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
v___jp_2281_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_nat_add(v___x_2268_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec(v___x_2268_);
v___x_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v_k_2234_);
lean_ctor_set(v___x_2284_, 2, v_v_2235_);
lean_ctor_set(v___x_2284_, 3, v_l_2236_);
lean_ctor_set(v___x_2284_, 4, v_l_2258_);
v___x_2285_ = lean_nat_add(v___x_2267_, v_size_2260_);
if (lean_obj_tag(v_r_2259_) == 0)
{
lean_object* v_size_2286_; 
v_size_2286_ = lean_ctor_get(v_r_2259_, 0);
lean_inc(v_size_2286_);
v___y_2271_ = v___x_2285_;
v___y_2272_ = v___x_2284_;
v___y_2273_ = v_size_2286_;
goto v___jp_2270_;
}
else
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_unsigned_to_nat(0u);
v___y_2271_ = v___x_2285_;
v___y_2272_ = v___x_2284_;
v___y_2273_ = v___x_2287_;
goto v___jp_2270_;
}
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_nat_add(v___x_2296_, v_size_2238_);
v___x_2298_ = lean_nat_add(v___x_2297_, v_size_2239_);
lean_dec(v_size_2239_);
v___x_2299_ = lean_nat_add(v___x_2297_, v_size_2255_);
lean_dec(v___x_2297_);
lean_inc_ref(v_l_2236_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 4, v_l_2242_);
lean_ctor_set(v___x_2252_, 3, v_l_2236_);
lean_ctor_set(v___x_2252_, 2, v_v_2235_);
lean_ctor_set(v___x_2252_, 1, v_k_2234_);
lean_ctor_set(v___x_2252_, 0, v___x_2299_);
v___x_2301_ = v___x_2252_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_v_2235_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_l_2236_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_l_2242_);
v___x_2301_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
v_isSharedCheck_2308_ = !lean_is_exclusive(v_l_2236_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; lean_object* v_unused_2310_; lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; 
v_unused_2309_ = lean_ctor_get(v_l_2236_, 4);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_l_2236_, 3);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_l_2236_, 2);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_l_2236_, 1);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_l_2236_, 0);
lean_dec(v_unused_2313_);
v___x_2303_ = v_l_2236_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_dec(v_l_2236_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 4, v_r_2243_);
lean_ctor_set(v___x_2303_, 3, v___x_2301_);
lean_ctor_set(v___x_2303_, 2, v_v_2241_);
lean_ctor_set(v___x_2303_, 1, v_k_2240_);
lean_ctor_set(v___x_2303_, 0, v___x_2298_);
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_r_2243_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_dec_ref_known(v_l_2242_, 5);
lean_del_object(v___x_2252_);
lean_dec(v_v_2241_);
lean_dec(v_k_2240_);
lean_dec(v_size_2239_);
lean_dec_ref_known(v_l_2236_, 5);
lean_dec(v_v_2235_);
lean_dec(v_k_2234_);
v___x_2315_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__2);
v___x_2316_ = l_panic___redArg(v___x_2254_, v___x_2315_);
return v___x_2316_;
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_del_object(v___x_2252_);
lean_dec(v_r_2243_);
lean_dec(v_v_2241_);
lean_dec(v_k_2240_);
lean_dec(v_size_2239_);
lean_dec_ref_known(v_l_2236_, 5);
lean_dec(v_v_2235_);
lean_dec(v_k_2234_);
v___x_2317_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_balanceR_x21___redArg___closed__3);
v___x_2318_ = l_panic___redArg(v___x_2254_, v___x_2317_);
return v___x_2318_;
}
}
}
}
else
{
lean_object* v_size_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_size_2325_ = lean_ctor_get(v_l_2236_, 0);
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_add(v___x_2326_, v_size_2325_);
v___x_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v_k_2234_);
lean_ctor_set(v___x_2328_, 2, v_v_2235_);
lean_ctor_set(v___x_2328_, 3, v_l_2236_);
lean_ctor_set(v___x_2328_, 4, v_r_2237_);
return v___x_2328_;
}
}
else
{
if (lean_obj_tag(v_r_2237_) == 0)
{
lean_object* v_l_2329_; 
v_l_2329_ = lean_ctor_get(v_r_2237_, 3);
lean_inc(v_l_2329_);
if (lean_obj_tag(v_l_2329_) == 0)
{
lean_object* v_r_2330_; 
v_r_2330_ = lean_ctor_get(v_r_2237_, 4);
lean_inc(v_r_2330_);
if (lean_obj_tag(v_r_2330_) == 0)
{
lean_object* v_size_2331_; lean_object* v_k_2332_; lean_object* v_v_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2345_; 
v_size_2331_ = lean_ctor_get(v_r_2237_, 0);
v_k_2332_ = lean_ctor_get(v_r_2237_, 1);
v_v_2333_ = lean_ctor_get(v_r_2237_, 2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_r_2237_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; lean_object* v_unused_2347_; 
v_unused_2346_ = lean_ctor_get(v_r_2237_, 4);
lean_dec(v_unused_2346_);
v_unused_2347_ = lean_ctor_get(v_r_2237_, 3);
lean_dec(v_unused_2347_);
v___x_2335_ = v_r_2237_;
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_v_2333_);
lean_inc(v_k_2332_);
lean_inc(v_size_2331_);
lean_dec(v_r_2237_);
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
lean_ctor_set(v___x_2335_, 3, v_l_2236_);
lean_ctor_set(v___x_2335_, 2, v_v_2235_);
lean_ctor_set(v___x_2335_, 1, v_k_2234_);
lean_ctor_set(v___x_2335_, 0, v___x_2340_);
v___x_2342_ = v___x_2335_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_v_2235_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_l_2236_);
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
v_k_2348_ = lean_ctor_get(v_r_2237_, 1);
v_v_2349_ = lean_ctor_get(v_r_2237_, 2);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_r_2237_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; lean_object* v_unused_2373_; lean_object* v_unused_2374_; 
v_unused_2372_ = lean_ctor_get(v_r_2237_, 4);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_r_2237_, 3);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_r_2237_, 0);
lean_dec(v_unused_2374_);
v___x_2351_ = v_r_2237_;
v_isShared_2352_ = v_isSharedCheck_2371_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_v_2349_);
lean_inc(v_k_2348_);
lean_dec(v_r_2237_);
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
lean_ctor_set(v___x_2356_, 2, v_v_2235_);
lean_ctor_set(v___x_2356_, 1, v_k_2234_);
lean_ctor_set(v___x_2356_, 0, v___x_2359_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2235_);
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
v_r_2375_ = lean_ctor_get(v_r_2237_, 4);
lean_inc(v_r_2375_);
if (lean_obj_tag(v_r_2375_) == 0)
{
lean_object* v_k_2376_; lean_object* v_v_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2387_; 
v_k_2376_ = lean_ctor_get(v_r_2237_, 1);
v_v_2377_ = lean_ctor_get(v_r_2237_, 2);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_r_2237_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; lean_object* v_unused_2389_; lean_object* v_unused_2390_; 
v_unused_2388_ = lean_ctor_get(v_r_2237_, 4);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_r_2237_, 3);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_r_2237_, 0);
lean_dec(v_unused_2390_);
v___x_2379_ = v_r_2237_;
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_v_2377_);
lean_inc(v_k_2376_);
lean_dec(v_r_2237_);
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
lean_ctor_set(v___x_2379_, 2, v_v_2235_);
lean_ctor_set(v___x_2379_, 1, v_k_2234_);
lean_ctor_set(v___x_2379_, 0, v___x_2382_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2235_);
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
lean_ctor_set(v___x_2392_, 1, v_k_2234_);
lean_ctor_set(v___x_2392_, 2, v_v_2235_);
lean_ctor_set(v___x_2392_, 3, v_r_2375_);
lean_ctor_set(v___x_2392_, 4, v_r_2237_);
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
lean_ctor_set(v___x_2394_, 1, v_k_2234_);
lean_ctor_set(v___x_2394_, 2, v_v_2235_);
lean_ctor_set(v___x_2394_, 3, v_r_2237_);
lean_ctor_set(v___x_2394_, 4, v_r_2237_);
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
v___x_2440_ = lean_nat_add(v___y_2437_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec(v___y_2437_);
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
lean_ctor_set(v___x_2444_, 3, v___y_2438_);
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
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v___y_2438_);
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
v___y_2437_ = v___x_2462_;
v___y_2438_ = v___x_2461_;
v___y_2439_ = v_size_2463_;
goto v___jp_2436_;
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___y_2437_ = v___x_2462_;
v___y_2438_ = v___x_2461_;
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
v___x_2511_ = lean_nat_add(v___y_2508_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec(v___y_2508_);
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
lean_ctor_set(v___x_2490_, 3, v___y_2509_);
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
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v___y_2509_);
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
v___y_2508_ = v___x_2522_;
v___y_2509_ = v___x_2521_;
v___y_2510_ = v_size_2523_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_unsigned_to_nat(0u);
v___y_2508_ = v___x_2522_;
v___y_2509_ = v___x_2521_;
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
v___x_2711_ = lean_panic_fn_borrowed(v___x_2710_, v_msg_2709_);
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
v___x_2787_ = lean_nat_add(v___y_2784_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec(v___y_2784_);
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
lean_ctor_set(v___x_2791_, 3, v___y_2785_);
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
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v___y_2785_);
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
v___y_2784_ = v___x_2809_;
v___y_2785_ = v___x_2808_;
v___y_2786_ = v_size_2810_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_unsigned_to_nat(0u);
v___y_2784_ = v___x_2809_;
v___y_2785_ = v___x_2808_;
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
lean_dec_ref_known(v_l_2749_, 5);
lean_del_object(v___x_2766_);
lean_dec(v_v_2748_);
lean_dec(v_k_2747_);
lean_dec_ref_known(v_r_2745_, 5);
lean_dec(v_size_2746_);
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
lean_dec_ref_known(v_r_2745_, 5);
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
lean_dec_ref_known(v_l_2754_, 5);
lean_del_object(v___x_2841_);
lean_dec(v_v_2753_);
lean_dec(v_k_2752_);
lean_dec(v_size_2751_);
lean_dec_ref_known(v_l_2744_, 5);
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
lean_dec_ref_known(v_l_2744_, 5);
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
lean_dec_ref_known(v_rl_3180_, 5);
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
lean_dec_ref_known(v_l_3212_, 5);
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
lean_dec_ref_known(v_l_3226_, 5);
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
lean_dec_ref_known(v_lr_3242_, 5);
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
lean_dec_ref_known(v_r_3314_, 5);
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
lean_dec_ref_known(v_l_3320_, 5);
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
lean_dec_ref_known(v_r_3321_, 5);
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
lean_dec_ref_known(v_r_3314_, 5);
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
lean_dec_ref_known(v_l_3320_, 5);
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
lean_dec_ref_known(v_r_3314_, 5);
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
lean_dec_ref_known(v_r_3345_, 5);
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
lean_dec_ref_known(v_r_3314_, 5);
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
lean_dec_ref_known(v_r_3364_, 5);
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
lean_dec_ref_known(v_l_3370_, 5);
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
lean_dec_ref_known(v_r_3371_, 5);
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
lean_dec_ref_known(v_r_3364_, 5);
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
lean_dec_ref_known(v_l_3370_, 5);
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
lean_dec_ref_known(v_r_3364_, 5);
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
lean_dec_ref_known(v_r_3395_, 5);
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
lean_dec_ref_known(v_r_3364_, 5);
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
lean_dec_ref_known(v_ll_3411_, 5);
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
lean_dec_ref_known(v_lr_3412_, 5);
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
lean_dec_ref_known(v_ll_3411_, 5);
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
lean_dec_ref_known(v_lr_3412_, 5);
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
lean_dec_ref_known(v_ll_3445_, 5);
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
lean_dec_ref_known(v_lr_3446_, 5);
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
lean_dec_ref_known(v_ll_3445_, 5);
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
lean_dec_ref_known(v_lr_3446_, 5);
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
lean_dec_ref_known(v_ll_3476_, 5);
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
lean_dec_ref_known(v_lr_3477_, 5);
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
lean_dec_ref_known(v_ll_3476_, 5);
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
lean_dec_ref_known(v_ll_3502_, 5);
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
lean_dec_ref_known(v_lr_3503_, 5);
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
lean_dec_ref_known(v_ll_3502_, 5);
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
lean_dec_ref_known(v_r_3525_, 5);
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
lean_dec_ref_known(v_r_3539_, 5);
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
lean_dec_ref_known(v_l_3561_, 5);
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
lean_dec_ref_known(v_l_3567_, 5);
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
lean_dec_ref_known(v_r_3568_, 5);
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
lean_dec_ref_known(v_l_3561_, 5);
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
lean_dec_ref_known(v_l_3567_, 5);
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
lean_dec_ref_known(v_l_3561_, 5);
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
lean_dec_ref_known(v_r_3592_, 5);
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
lean_dec_ref_known(v_l_3561_, 5);
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
lean_dec_ref_known(v_l_3610_, 5);
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
lean_dec_ref_known(v_l_3618_, 5);
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
lean_dec_ref_known(v_r_3619_, 5);
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
lean_dec_ref_known(v_l_3610_, 5);
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
lean_dec_ref_known(v_l_3618_, 5);
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
lean_dec_ref_known(v_l_3610_, 5);
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
lean_dec_ref_known(v_r_3643_, 5);
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
lean_dec_ref_known(v_l_3610_, 5);
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
lean_dec_ref_known(v_l_3658_, 5);
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
lean_dec_ref_known(v_l_3676_, 5);
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
lean_dec_ref_known(v_ll_3702_, 5);
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
lean_dec_ref_known(v_lr_3703_, 5);
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
lean_dec_ref_known(v_ll_3702_, 5);
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
lean_dec_ref_known(v_ll_3736_, 5);
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
lean_dec_ref_known(v_lr_3737_, 5);
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
lean_dec_ref_known(v_ll_3736_, 5);
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
lean_dec_ref_known(v_l_3780_, 5);
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
lean_dec_ref_known(v_l_3786_, 5);
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
lean_dec_ref_known(v_r_3787_, 5);
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
lean_dec_ref_known(v_l_3780_, 5);
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
lean_dec_ref_known(v_l_3786_, 5);
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
lean_dec_ref_known(v_l_3780_, 5);
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
lean_dec_ref_known(v_r_3811_, 5);
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
lean_dec_ref_known(v_l_3780_, 5);
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
lean_dec_ref_known(v_l_3830_, 5);
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
lean_dec_ref_known(v_l_3836_, 5);
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
lean_dec_ref_known(v_r_3837_, 5);
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
lean_dec_ref_known(v_l_3830_, 5);
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
lean_dec_ref_known(v_l_3836_, 5);
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
lean_dec_ref_known(v_l_3830_, 5);
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
lean_dec_ref_known(v_r_3861_, 5);
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
lean_dec_ref_known(v_l_3830_, 5);
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
lean_dec_ref_known(v_ll_3877_, 5);
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
lean_dec_ref_known(v_lr_3878_, 5);
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
lean_dec_ref_known(v_ll_3877_, 5);
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
lean_dec_ref_known(v_ll_3911_, 5);
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
lean_dec_ref_known(v_lr_3912_, 5);
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
lean_dec_ref_known(v_ll_3911_, 5);
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
lean_dec_ref_known(v_r_3955_, 5);
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
lean_dec_ref_known(v_l_3961_, 5);
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
lean_dec_ref_known(v_r_3962_, 5);
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
lean_dec_ref_known(v_r_3955_, 5);
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
lean_dec_ref_known(v_l_3961_, 5);
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
lean_dec_ref_known(v_r_3955_, 5);
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
lean_dec_ref_known(v_r_3986_, 5);
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
lean_dec_ref_known(v_r_3955_, 5);
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
lean_dec_ref_known(v_r_4004_, 5);
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
lean_dec_ref_known(v_l_4012_, 5);
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
lean_dec_ref_known(v_r_4013_, 5);
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
lean_dec_ref_known(v_r_4004_, 5);
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
lean_dec_ref_known(v_l_4012_, 5);
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
lean_dec_ref_known(v_r_4004_, 5);
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
lean_dec_ref_known(v_r_4037_, 5);
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
lean_dec_ref_known(v_r_4004_, 5);
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
lean_dec_ref_known(v_r_4052_, 5);
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
lean_dec_ref_known(v_r_4066_, 5);
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
lean_dec_ref_known(v_r_4088_, 5);
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
lean_dec_ref_known(v_l_4094_, 5);
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
lean_dec_ref_known(v_r_4095_, 5);
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
lean_dec_ref_known(v_r_4088_, 5);
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
lean_dec_ref_known(v_l_4094_, 5);
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
lean_dec_ref_known(v_r_4088_, 5);
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
lean_dec_ref_known(v_r_4119_, 5);
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
lean_dec_ref_known(v_r_4088_, 5);
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
lean_dec_ref_known(v_r_4137_, 5);
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
lean_dec_ref_known(v_l_4145_, 5);
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
lean_dec_ref_known(v_r_4146_, 5);
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
lean_dec_ref_known(v_r_4137_, 5);
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
lean_dec_ref_known(v_l_4145_, 5);
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
lean_dec_ref_known(v_r_4137_, 5);
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
lean_dec_ref_known(v_r_4170_, 5);
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
lean_dec_ref_known(v_r_4137_, 5);
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
lean_dec_ref_known(v_l_4185_, 5);
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
lean_dec_ref_known(v_l_4203_, 5);
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
lean_dec_ref_known(v_r_4229_, 5);
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
lean_dec_ref_known(v_l_4235_, 5);
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
lean_dec_ref_known(v_r_4236_, 5);
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
lean_dec_ref_known(v_r_4229_, 5);
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
lean_dec_ref_known(v_l_4235_, 5);
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
lean_dec_ref_known(v_r_4229_, 5);
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
lean_dec_ref_known(v_r_4260_, 5);
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
lean_dec_ref_known(v_r_4229_, 5);
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
lean_dec_ref_known(v_r_4279_, 5);
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
lean_dec_ref_known(v_l_4285_, 5);
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
lean_dec_ref_known(v_r_4286_, 5);
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
lean_dec_ref_known(v_r_4279_, 5);
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
lean_dec_ref_known(v_l_4285_, 5);
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
lean_dec_ref_known(v_r_4279_, 5);
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
lean_dec_ref_known(v_r_4310_, 5);
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
lean_dec_ref_known(v_r_4279_, 5);
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
lean_dec_ref_known(v_r_4326_, 5);
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
lean_dec_ref_known(v_r_4340_, 5);
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
lean_dec_ref_known(v_l_4360_, 5);
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
lean_dec_ref_known(v_l_4374_, 5);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Balancing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
