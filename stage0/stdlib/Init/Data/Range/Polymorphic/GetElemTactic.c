// Lean compiler output
// Module: Init.Data.Range.Polymorphic.GetElemTactic
// Imports: public meta import Init.Grind.Tactics public import Init.Data.Range.Polymorphic.Basic public import Init.Data.Vector.Basic public import Init.Data.Slice.Array.Lemmas
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "tacticGet_elem_tactic_extensible"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 80, 20, 121, 148, 193, 237, 106)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rwRule"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(163, 12, 102, 31, 194, 63, 248, 122)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Rcc.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rcc"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(24, 238, 58, 56, 209, 114, 29, 228)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(217, 204, 98, 3, 79, 211, 113, 170)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(134, 218, 71, 35, 220, 118, 132, 17)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Rco.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rco"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(82, 23, 146, 9, 98, 233, 127, 0)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(235, 4, 110, 87, 96, 137, 227, 12)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Rci.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rci"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(83, 90, 19, 212, 182, 193, 89, 16)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(86, 68, 124, 226, 69, 44, 173, 245)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Roc.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Roc"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(28, 166, 87, 113, 118, 177, 150, 230)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(133, 62, 136, 193, 167, 220, 170, 158)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Roo.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Roo"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(142, 134, 1, 143, 80, 181, 102, 249)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(223, 162, 61, 47, 17, 109, 12, 229)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__67_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Roi.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Roi"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(95, 65, 216, 85, 31, 94, 16, 225)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(90, 238, 255, 162, 106, 104, 142, 122)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__73_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Ric.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ric"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__77_value),LEAN_SCALAR_PTR_LITERAL(185, 67, 230, 246, 155, 76, 10, 120)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(36, 202, 71, 89, 148, 250, 181, 110)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Rio.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rio"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__83_value),LEAN_SCALAR_PTR_LITERAL(129, 16, 150, 7, 181, 46, 199, 145)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(28, 127, 22, 133, 217, 4, 252, 106)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__85_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Std.Rii.mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rii"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value),LEAN_SCALAR_PTR_LITERAL(204, 10, 192, 182, 218, 42, 98, 220)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(245, 8, 90, 202, 101, 174, 1, 128)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__89_value),LEAN_SCALAR_PTR_LITERAL(204, 10, 192, 182, 218, 42, 98, 220)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__91_value),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__92_value)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__93_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95_value),LEAN_SCALAR_PTR_LITERAL(246, 53, 215, 155, 171, 182, 123, 76)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__97_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__99_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "zetaDelta"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102_value),LEAN_SCALAR_PTR_LITERAL(129, 80, 40, 32, 247, 216, 203, 14)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__106_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Vector.size"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Vector"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__110_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__111_value),LEAN_SCALAR_PTR_LITERAL(172, 82, 10, 197, 101, 115, 192, 27)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__113_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_rco"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_rco"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(202, 71, 19, 170, 78, 65, 66, 253)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__122_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_rcc"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_rcc"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(63, 213, 142, 122, 202, 158, 57, 225)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__129_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_rci"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_rci"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__133_value),LEAN_SCALAR_PTR_LITERAL(6, 119, 80, 20, 101, 99, 67, 112)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__135_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_roo"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_roo"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__139_value),LEAN_SCALAR_PTR_LITERAL(112, 214, 247, 86, 232, 119, 121, 11)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__141_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_roc"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_roc"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__145_value),LEAN_SCALAR_PTR_LITERAL(162, 148, 127, 170, 252, 221, 249, 26)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__147_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_roi"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_roi"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__151_value),LEAN_SCALAR_PTR_LITERAL(142, 38, 124, 222, 139, 68, 226, 128)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__153_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_rio"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_rio"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__157_value),LEAN_SCALAR_PTR_LITERAL(139, 244, 2, 77, 6, 57, 41, 32)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__159_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_ric"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_ric"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__163_value),LEAN_SCALAR_PTR_LITERAL(27, 195, 104, 204, 208, 115, 201, 174)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__165_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.size_mkSlice_rii"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "size_mkSlice_rii"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__169_value),LEAN_SCALAR_PTR_LITERAL(140, 227, 52, 233, 69, 69, 46, 14)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__171_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Array_mkArray0(lean_box(0));
return v___x_52_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30));
v___x_68_ = l_String_toRawSubstring_x27(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45));
v___x_99_ = l_String_toRawSubstring_x27(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51));
v___x_113_ = l_String_toRawSubstring_x27(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57));
v___x_127_ = l_String_toRawSubstring_x27(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63));
v___x_141_ = l_String_toRawSubstring_x27(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69));
v___x_155_ = l_String_toRawSubstring_x27(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75));
v___x_169_ = l_String_toRawSubstring_x27(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81));
v___x_183_ = l_String_toRawSubstring_x27(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87));
v___x_197_ = l_String_toRawSubstring_x27(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102));
v___x_236_ = l_String_toRawSubstring_x27(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108));
v___x_248_ = l_String_toRawSubstring_x27(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117));
v___x_268_ = l_String_toRawSubstring_x27(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125));
v___x_283_ = l_String_toRawSubstring_x27(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131));
v___x_296_ = l_String_toRawSubstring_x27(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137));
v___x_309_ = l_String_toRawSubstring_x27(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143));
v___x_322_ = l_String_toRawSubstring_x27(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149));
v___x_335_ = l_String_toRawSubstring_x27(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155));
v___x_348_ = l_String_toRawSubstring_x27(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161));
v___x_361_ = l_String_toRawSubstring_x27(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167));
v___x_374_ = l_String_toRawSubstring_x27(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_401_ = l_Lean_Syntax_isOfKind(v_x_397_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_box(1);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_a_399_);
return v___x_403_;
}
else
{
lean_object* v_quotContext_404_; lean_object* v_currMacroScope_405_; lean_object* v_ref_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_quotContext_404_ = lean_ctor_get(v_a_398_, 1);
v_currMacroScope_405_ = lean_ctor_get(v_a_398_, 2);
v_ref_406_ = lean_ctor_get(v_a_398_, 5);
v___x_407_ = 0;
v___x_408_ = l_Lean_SourceInfo_fromRef(v_ref_406_, v___x_407_);
v___x_409_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5));
v___x_410_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
lean_inc_n(v___x_408_, 152);
v___x_411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_408_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
v___x_412_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
v___x_413_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_414_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11));
v___x_415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_408_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13));
v___x_417_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15));
v___x_418_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
v___x_419_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
v___x_420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_408_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
v___x_422_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21));
v___x_423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_408_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23));
v___x_425_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24);
v___x_426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_426_, 0, v___x_408_);
lean_ctor_set(v___x_426_, 1, v___x_412_);
lean_ctor_set(v___x_426_, 2, v___x_425_);
lean_inc_ref_n(v___x_426_, 43);
v___x_427_ = l_Lean_Syntax_node1(v___x_408_, v___x_424_, v___x_426_);
v___x_428_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26));
v___x_429_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27));
v___x_430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_408_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29));
v___x_432_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31);
v___x_433_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35));
lean_inc_n(v_currMacroScope_405_, 20);
lean_inc_n(v_quotContext_404_, 20);
v___x_434_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_433_, v_currMacroScope_405_);
v___x_435_ = lean_box(0);
v___x_436_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37));
v___x_437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_437_, 0, v___x_408_);
lean_ctor_set(v___x_437_, 1, v___x_432_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
lean_ctor_set(v___x_437_, 3, v___x_436_);
v___x_438_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_437_);
v___x_439_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_438_);
v___x_440_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38));
v___x_441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_408_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_inc_ref_n(v___x_441_, 10);
lean_inc_ref_n(v___x_430_, 10);
v___x_442_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_439_, v___x_441_);
v___x_443_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40));
v___x_444_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41));
v___x_445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_408_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43));
v___x_447_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44));
v___x_448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_408_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_Syntax_node1(v___x_408_, v___x_446_, v___x_448_);
v___x_450_ = l_Lean_Syntax_node2(v___x_408_, v___x_443_, v___x_445_, v___x_449_);
v___x_451_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_450_);
lean_inc_n(v___x_451_, 9);
lean_inc_n(v___x_427_, 10);
lean_inc_ref_n(v___x_423_, 8);
v___x_452_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_442_, v___x_451_);
v___x_453_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_452_);
v___x_454_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_453_);
v___x_455_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_454_);
lean_inc_ref_n(v___x_420_, 10);
v___x_456_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_455_);
v___x_457_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46);
v___x_458_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48));
v___x_459_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_458_, v_currMacroScope_405_);
v___x_460_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50));
v___x_461_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_461_, 0, v___x_408_);
lean_ctor_set(v___x_461_, 1, v___x_457_);
lean_ctor_set(v___x_461_, 2, v___x_459_);
lean_ctor_set(v___x_461_, 3, v___x_460_);
v___x_462_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_461_);
v___x_463_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_462_);
v___x_464_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_463_, v___x_441_);
v___x_465_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_464_, v___x_451_);
v___x_466_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_465_);
v___x_467_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_466_);
v___x_468_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_468_);
v___x_470_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52);
v___x_471_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54));
v___x_472_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_471_, v_currMacroScope_405_);
v___x_473_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56));
v___x_474_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_474_, 0, v___x_408_);
lean_ctor_set(v___x_474_, 1, v___x_470_);
lean_ctor_set(v___x_474_, 2, v___x_472_);
lean_ctor_set(v___x_474_, 3, v___x_473_);
v___x_475_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_474_);
v___x_476_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_475_);
v___x_477_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_476_, v___x_441_);
v___x_478_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_477_, v___x_451_);
v___x_479_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_478_);
v___x_480_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_479_);
v___x_481_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_480_);
v___x_482_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_481_);
v___x_483_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58);
v___x_484_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60));
v___x_485_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_484_, v_currMacroScope_405_);
v___x_486_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62));
v___x_487_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_487_, 0, v___x_408_);
lean_ctor_set(v___x_487_, 1, v___x_483_);
lean_ctor_set(v___x_487_, 2, v___x_485_);
lean_ctor_set(v___x_487_, 3, v___x_486_);
v___x_488_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_487_);
v___x_489_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_488_);
v___x_490_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_489_, v___x_441_);
v___x_491_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_490_, v___x_451_);
v___x_492_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_491_);
v___x_493_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_492_);
v___x_494_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_493_);
v___x_495_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_494_);
v___x_496_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64);
v___x_497_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66));
v___x_498_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_497_, v_currMacroScope_405_);
v___x_499_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68));
v___x_500_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_500_, 0, v___x_408_);
lean_ctor_set(v___x_500_, 1, v___x_496_);
lean_ctor_set(v___x_500_, 2, v___x_498_);
lean_ctor_set(v___x_500_, 3, v___x_499_);
v___x_501_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_500_);
v___x_502_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_501_);
v___x_503_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_502_, v___x_441_);
v___x_504_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_503_, v___x_451_);
v___x_505_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_504_);
v___x_506_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_505_);
v___x_507_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_506_);
v___x_508_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_507_);
v___x_509_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70);
v___x_510_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72));
v___x_511_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_510_, v_currMacroScope_405_);
v___x_512_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74));
v___x_513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_513_, 0, v___x_408_);
lean_ctor_set(v___x_513_, 1, v___x_509_);
lean_ctor_set(v___x_513_, 2, v___x_511_);
lean_ctor_set(v___x_513_, 3, v___x_512_);
v___x_514_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_513_);
v___x_515_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_514_);
v___x_516_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_515_, v___x_441_);
v___x_517_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_516_, v___x_451_);
v___x_518_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_517_);
v___x_519_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_518_);
v___x_520_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_519_);
v___x_521_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_520_);
v___x_522_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76);
v___x_523_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78));
v___x_524_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_523_, v_currMacroScope_405_);
v___x_525_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80));
v___x_526_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_526_, 0, v___x_408_);
lean_ctor_set(v___x_526_, 1, v___x_522_);
lean_ctor_set(v___x_526_, 2, v___x_524_);
lean_ctor_set(v___x_526_, 3, v___x_525_);
v___x_527_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_526_);
v___x_528_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_527_);
v___x_529_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_528_, v___x_441_);
v___x_530_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_529_, v___x_451_);
v___x_531_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_530_);
v___x_532_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_531_);
v___x_533_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_532_);
v___x_534_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_533_);
v___x_535_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82);
v___x_536_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84));
v___x_537_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_536_, v_currMacroScope_405_);
v___x_538_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86));
v___x_539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_539_, 0, v___x_408_);
lean_ctor_set(v___x_539_, 1, v___x_535_);
lean_ctor_set(v___x_539_, 2, v___x_537_);
lean_ctor_set(v___x_539_, 3, v___x_538_);
v___x_540_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_541_, v___x_441_);
v___x_543_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_542_, v___x_451_);
v___x_544_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_543_);
v___x_545_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_544_);
v___x_546_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_546_);
v___x_548_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88);
v___x_549_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90));
v___x_550_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_549_, v_currMacroScope_405_);
v___x_551_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94));
v___x_552_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_552_, 0, v___x_408_);
lean_ctor_set(v___x_552_, 1, v___x_548_);
lean_ctor_set(v___x_552_, 2, v___x_550_);
lean_ctor_set(v___x_552_, 3, v___x_551_);
v___x_553_ = l_Lean_Syntax_node2(v___x_408_, v___x_431_, v___x_426_, v___x_552_);
v___x_554_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_553_);
v___x_555_ = l_Lean_Syntax_node3(v___x_408_, v___x_428_, v___x_430_, v___x_554_, v___x_441_);
v___x_556_ = l_Lean_Syntax_node4(v___x_408_, v___x_421_, v___x_423_, v___x_427_, v___x_555_, v___x_451_);
v___x_557_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_556_);
v___x_558_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_557_);
v___x_559_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_558_);
v___x_560_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_559_);
v___x_561_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95));
v___x_562_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96));
v___x_563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_408_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
v___x_564_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98));
v___x_565_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100));
v___x_566_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101));
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_408_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103);
v___x_569_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104));
v___x_570_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_569_, v_currMacroScope_405_);
v___x_571_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_571_, 0, v___x_408_);
lean_ctor_set(v___x_571_, 1, v___x_568_);
lean_ctor_set(v___x_571_, 2, v___x_570_);
lean_ctor_set(v___x_571_, 3, v___x_435_);
v___x_572_ = l_Lean_Syntax_node2(v___x_408_, v___x_565_, v___x_567_, v___x_571_);
v___x_573_ = l_Lean_Syntax_node1(v___x_408_, v___x_564_, v___x_572_);
v___x_574_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_573_);
v___x_575_ = l_Lean_Syntax_node1(v___x_408_, v___x_424_, v___x_574_);
v___x_576_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_408_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_577_);
v___x_579_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107));
v___x_580_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109);
v___x_581_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112));
v___x_582_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_581_, v_currMacroScope_405_);
v___x_583_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114));
v___x_584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_584_, 0, v___x_408_);
lean_ctor_set(v___x_584_, 1, v___x_580_);
lean_ctor_set(v___x_584_, 2, v___x_582_);
lean_ctor_set(v___x_584_, 3, v___x_583_);
v___x_585_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_584_);
v___x_586_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_585_);
v___x_587_ = l_Lean_Syntax_node3(v___x_408_, v___x_412_, v___x_430_, v___x_586_, v___x_441_);
lean_inc(v___x_578_);
v___x_588_ = l_Lean_Syntax_node6(v___x_408_, v___x_562_, v___x_563_, v___x_575_, v___x_426_, v___x_578_, v___x_587_, v___x_451_);
v___x_589_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_588_);
v___x_590_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_589_);
v___x_591_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_590_);
v___x_592_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_591_);
v___x_593_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115));
v___x_594_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116));
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_408_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
v___x_596_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118);
v___x_597_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121));
v___x_598_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_597_, v_currMacroScope_405_);
v___x_599_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123));
v___x_600_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_600_, 0, v___x_408_);
lean_ctor_set(v___x_600_, 1, v___x_596_);
lean_ctor_set(v___x_600_, 2, v___x_598_);
lean_ctor_set(v___x_600_, 3, v___x_599_);
v___x_601_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_600_);
v___x_602_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124));
v___x_603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_408_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126);
v___x_605_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128));
v___x_606_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_605_, v_currMacroScope_405_);
v___x_607_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130));
v___x_608_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_608_, 0, v___x_408_);
lean_ctor_set(v___x_608_, 1, v___x_604_);
lean_ctor_set(v___x_608_, 2, v___x_606_);
lean_ctor_set(v___x_608_, 3, v___x_607_);
v___x_609_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_608_);
v___x_610_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132);
v___x_611_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134));
v___x_612_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_611_, v_currMacroScope_405_);
v___x_613_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136));
v___x_614_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_614_, 0, v___x_408_);
lean_ctor_set(v___x_614_, 1, v___x_610_);
lean_ctor_set(v___x_614_, 2, v___x_612_);
lean_ctor_set(v___x_614_, 3, v___x_613_);
v___x_615_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_614_);
v___x_616_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138);
v___x_617_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140));
v___x_618_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_617_, v_currMacroScope_405_);
v___x_619_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142));
v___x_620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_620_, 0, v___x_408_);
lean_ctor_set(v___x_620_, 1, v___x_616_);
lean_ctor_set(v___x_620_, 2, v___x_618_);
lean_ctor_set(v___x_620_, 3, v___x_619_);
v___x_621_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_620_);
v___x_622_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144);
v___x_623_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146));
v___x_624_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_623_, v_currMacroScope_405_);
v___x_625_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148));
v___x_626_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_626_, 0, v___x_408_);
lean_ctor_set(v___x_626_, 1, v___x_622_);
lean_ctor_set(v___x_626_, 2, v___x_624_);
lean_ctor_set(v___x_626_, 3, v___x_625_);
v___x_627_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_626_);
v___x_628_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150);
v___x_629_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152));
v___x_630_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_629_, v_currMacroScope_405_);
v___x_631_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154));
v___x_632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_632_, 0, v___x_408_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_630_);
lean_ctor_set(v___x_632_, 3, v___x_631_);
v___x_633_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_632_);
v___x_634_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156);
v___x_635_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158));
v___x_636_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_635_, v_currMacroScope_405_);
v___x_637_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160));
v___x_638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_638_, 0, v___x_408_);
lean_ctor_set(v___x_638_, 1, v___x_634_);
lean_ctor_set(v___x_638_, 2, v___x_636_);
lean_ctor_set(v___x_638_, 3, v___x_637_);
v___x_639_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_638_);
v___x_640_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162);
v___x_641_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164));
v___x_642_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_641_, v_currMacroScope_405_);
v___x_643_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166));
v___x_644_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_644_, 0, v___x_408_);
lean_ctor_set(v___x_644_, 1, v___x_640_);
lean_ctor_set(v___x_644_, 2, v___x_642_);
lean_ctor_set(v___x_644_, 3, v___x_643_);
v___x_645_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_644_);
v___x_646_ = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168);
v___x_647_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170));
v___x_648_ = l_Lean_addMacroScope(v_quotContext_404_, v___x_647_, v_currMacroScope_405_);
v___x_649_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172));
v___x_650_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_650_, 0, v___x_408_);
lean_ctor_set(v___x_650_, 1, v___x_646_);
lean_ctor_set(v___x_650_, 2, v___x_648_);
lean_ctor_set(v___x_650_, 3, v___x_649_);
v___x_651_ = l_Lean_Syntax_node3(v___x_408_, v___x_579_, v___x_426_, v___x_426_, v___x_650_);
v___x_652_ = lean_unsigned_to_nat(17u);
v___x_653_ = lean_mk_empty_array_with_capacity(v___x_652_);
v___x_654_ = lean_array_push(v___x_653_, v___x_601_);
lean_inc_ref_n(v___x_603_, 7);
v___x_655_ = lean_array_push(v___x_654_, v___x_603_);
v___x_656_ = lean_array_push(v___x_655_, v___x_609_);
v___x_657_ = lean_array_push(v___x_656_, v___x_603_);
v___x_658_ = lean_array_push(v___x_657_, v___x_615_);
v___x_659_ = lean_array_push(v___x_658_, v___x_603_);
v___x_660_ = lean_array_push(v___x_659_, v___x_621_);
v___x_661_ = lean_array_push(v___x_660_, v___x_603_);
v___x_662_ = lean_array_push(v___x_661_, v___x_627_);
v___x_663_ = lean_array_push(v___x_662_, v___x_603_);
v___x_664_ = lean_array_push(v___x_663_, v___x_633_);
v___x_665_ = lean_array_push(v___x_664_, v___x_603_);
v___x_666_ = lean_array_push(v___x_665_, v___x_639_);
v___x_667_ = lean_array_push(v___x_666_, v___x_603_);
v___x_668_ = lean_array_push(v___x_667_, v___x_645_);
v___x_669_ = lean_array_push(v___x_668_, v___x_603_);
v___x_670_ = lean_array_push(v___x_669_, v___x_651_);
v___x_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_671_, 0, v___x_408_);
lean_ctor_set(v___x_671_, 1, v___x_412_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
v___x_672_ = l_Lean_Syntax_node3(v___x_408_, v___x_412_, v___x_430_, v___x_671_, v___x_441_);
v___x_673_ = l_Lean_Syntax_node6(v___x_408_, v___x_594_, v___x_595_, v___x_427_, v___x_426_, v___x_578_, v___x_672_, v___x_426_);
v___x_674_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_673_);
v___x_675_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_674_);
v___x_676_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_675_);
v___x_677_ = l_Lean_Syntax_node2(v___x_408_, v___x_418_, v___x_420_, v___x_676_);
v___x_678_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173));
v___x_679_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174));
v___x_680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_408_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
v___x_681_ = l_Lean_Syntax_node2(v___x_408_, v___x_679_, v___x_680_, v___x_427_);
v___x_682_ = lean_unsigned_to_nat(23u);
v___x_683_ = lean_mk_empty_array_with_capacity(v___x_682_);
v___x_684_ = lean_array_push(v___x_683_, v___x_456_);
v___x_685_ = lean_array_push(v___x_684_, v___x_426_);
v___x_686_ = lean_array_push(v___x_685_, v___x_469_);
v___x_687_ = lean_array_push(v___x_686_, v___x_426_);
v___x_688_ = lean_array_push(v___x_687_, v___x_482_);
v___x_689_ = lean_array_push(v___x_688_, v___x_426_);
v___x_690_ = lean_array_push(v___x_689_, v___x_495_);
v___x_691_ = lean_array_push(v___x_690_, v___x_426_);
v___x_692_ = lean_array_push(v___x_691_, v___x_508_);
v___x_693_ = lean_array_push(v___x_692_, v___x_426_);
v___x_694_ = lean_array_push(v___x_693_, v___x_521_);
v___x_695_ = lean_array_push(v___x_694_, v___x_426_);
v___x_696_ = lean_array_push(v___x_695_, v___x_534_);
v___x_697_ = lean_array_push(v___x_696_, v___x_426_);
v___x_698_ = lean_array_push(v___x_697_, v___x_547_);
v___x_699_ = lean_array_push(v___x_698_, v___x_426_);
v___x_700_ = lean_array_push(v___x_699_, v___x_560_);
v___x_701_ = lean_array_push(v___x_700_, v___x_426_);
v___x_702_ = lean_array_push(v___x_701_, v___x_592_);
v___x_703_ = lean_array_push(v___x_702_, v___x_426_);
v___x_704_ = lean_array_push(v___x_703_, v___x_677_);
v___x_705_ = lean_array_push(v___x_704_, v___x_426_);
v___x_706_ = lean_array_push(v___x_705_, v___x_681_);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v___x_408_);
lean_ctor_set(v___x_707_, 1, v___x_412_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
v___x_708_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_707_);
v___x_709_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_708_);
lean_inc_ref(v___x_415_);
v___x_710_ = l_Lean_Syntax_node2(v___x_408_, v___x_413_, v___x_415_, v___x_709_);
v___x_711_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175));
v___x_712_ = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_408_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
v___x_714_ = l_Lean_Syntax_node1(v___x_408_, v___x_712_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node1(v___x_408_, v___x_412_, v___x_714_);
v___x_716_ = l_Lean_Syntax_node1(v___x_408_, v___x_417_, v___x_715_);
v___x_717_ = l_Lean_Syntax_node1(v___x_408_, v___x_416_, v___x_716_);
v___x_718_ = l_Lean_Syntax_node2(v___x_408_, v___x_413_, v___x_415_, v___x_717_);
v___x_719_ = l_Lean_Syntax_node2(v___x_408_, v___x_412_, v___x_710_, v___x_718_);
v___x_720_ = l_Lean_Syntax_node2(v___x_408_, v___x_410_, v___x_411_, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_a_399_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object* v_x_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1(v_x_722_, v_a_723_, v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_725_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
}
#ifdef __cplusplus
}
#endif
