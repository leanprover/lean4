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
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "tacticGet_elem_tactic_extensible"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__32_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rcc"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__33_value;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mem_iff"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__34_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175_value;
static lean_once_cell_t l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176;
static const lean_string_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__177 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__177_value;
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value_aux_1),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__177_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178 = (const lean_object*)&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__30));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__45));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__51));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__57));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__63));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__69));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__75));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__81));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__87));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__102));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__108));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__117));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__125));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__131));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__137));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__143));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__149));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__155));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__161));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__167));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(17u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
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
x_13 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5));
x_14 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
x_17 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
x_18 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11));
lean_inc(x_12);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13));
x_21 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15));
x_22 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
x_23 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
lean_inc(x_12);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
x_26 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__21));
lean_inc(x_12);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__23));
x_29 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__24);
lean_inc(x_12);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_29);
lean_inc_ref(x_30);
lean_inc(x_12);
x_31 = l_Lean_Syntax_node1(x_12, x_28, x_30);
x_32 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__26));
x_33 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__27));
lean_inc(x_12);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_33);
x_35 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__29));
x_36 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__31);
x_37 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__35));
lean_inc(x_9);
lean_inc(x_8);
x_38 = l_Lean_addMacroScope(x_8, x_37, x_9);
x_39 = lean_box(0);
x_40 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__37));
lean_inc(x_12);
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
lean_inc_ref(x_30);
lean_inc(x_12);
x_42 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_41);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node1(x_12, x_16, x_42);
x_44 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__38));
lean_inc(x_12);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_46 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_43, x_45);
x_47 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__40));
x_48 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__41));
lean_inc(x_12);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
x_50 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__43));
x_51 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__44));
lean_inc(x_12);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_12);
x_53 = l_Lean_Syntax_node1(x_12, x_50, x_52);
lean_inc(x_12);
x_54 = l_Lean_Syntax_node2(x_12, x_47, x_49, x_53);
lean_inc(x_12);
x_55 = l_Lean_Syntax_node1(x_12, x_16, x_54);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_56 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_46, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node1(x_12, x_16, x_56);
lean_inc(x_12);
x_58 = l_Lean_Syntax_node1(x_12, x_21, x_57);
lean_inc(x_12);
x_59 = l_Lean_Syntax_node1(x_12, x_20, x_58);
lean_inc_ref(x_24);
lean_inc(x_12);
x_60 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_59);
x_61 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__46);
x_62 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__48));
lean_inc(x_9);
lean_inc(x_8);
x_63 = l_Lean_addMacroScope(x_8, x_62, x_9);
x_64 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__50));
lean_inc(x_12);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_12);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
lean_inc_ref(x_30);
lean_inc(x_12);
x_66 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_65);
lean_inc(x_12);
x_67 = l_Lean_Syntax_node1(x_12, x_16, x_66);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_68 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_67, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_68, x_55);
lean_inc(x_12);
x_70 = l_Lean_Syntax_node1(x_12, x_16, x_69);
lean_inc(x_12);
x_71 = l_Lean_Syntax_node1(x_12, x_21, x_70);
lean_inc(x_12);
x_72 = l_Lean_Syntax_node1(x_12, x_20, x_71);
lean_inc_ref(x_24);
lean_inc(x_12);
x_73 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_72);
x_74 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__52);
x_75 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__54));
lean_inc(x_9);
lean_inc(x_8);
x_76 = l_Lean_addMacroScope(x_8, x_75, x_9);
x_77 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__56));
lean_inc(x_12);
x_78 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_78, 0, x_12);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_77);
lean_inc_ref(x_30);
lean_inc(x_12);
x_79 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_78);
lean_inc(x_12);
x_80 = l_Lean_Syntax_node1(x_12, x_16, x_79);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_81 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_80, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_82 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_81, x_55);
lean_inc(x_12);
x_83 = l_Lean_Syntax_node1(x_12, x_16, x_82);
lean_inc(x_12);
x_84 = l_Lean_Syntax_node1(x_12, x_21, x_83);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node1(x_12, x_20, x_84);
lean_inc_ref(x_24);
lean_inc(x_12);
x_86 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_85);
x_87 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__58);
x_88 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__60));
lean_inc(x_9);
lean_inc(x_8);
x_89 = l_Lean_addMacroScope(x_8, x_88, x_9);
x_90 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__62));
lean_inc(x_12);
x_91 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_91, 0, x_12);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set(x_91, 3, x_90);
lean_inc_ref(x_30);
lean_inc(x_12);
x_92 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_91);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node1(x_12, x_16, x_92);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_94 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_93, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_95 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_94, x_55);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node1(x_12, x_16, x_95);
lean_inc(x_12);
x_97 = l_Lean_Syntax_node1(x_12, x_21, x_96);
lean_inc(x_12);
x_98 = l_Lean_Syntax_node1(x_12, x_20, x_97);
lean_inc_ref(x_24);
lean_inc(x_12);
x_99 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_98);
x_100 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__64);
x_101 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__66));
lean_inc(x_9);
lean_inc(x_8);
x_102 = l_Lean_addMacroScope(x_8, x_101, x_9);
x_103 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__68));
lean_inc(x_12);
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_12);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_102);
lean_ctor_set(x_104, 3, x_103);
lean_inc_ref(x_30);
lean_inc(x_12);
x_105 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_104);
lean_inc(x_12);
x_106 = l_Lean_Syntax_node1(x_12, x_16, x_105);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_107 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_106, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_108 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_107, x_55);
lean_inc(x_12);
x_109 = l_Lean_Syntax_node1(x_12, x_16, x_108);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node1(x_12, x_21, x_109);
lean_inc(x_12);
x_111 = l_Lean_Syntax_node1(x_12, x_20, x_110);
lean_inc_ref(x_24);
lean_inc(x_12);
x_112 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_111);
x_113 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__70);
x_114 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__72));
lean_inc(x_9);
lean_inc(x_8);
x_115 = l_Lean_addMacroScope(x_8, x_114, x_9);
x_116 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__74));
lean_inc(x_12);
x_117 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_117, 0, x_12);
lean_ctor_set(x_117, 1, x_113);
lean_ctor_set(x_117, 2, x_115);
lean_ctor_set(x_117, 3, x_116);
lean_inc_ref(x_30);
lean_inc(x_12);
x_118 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_117);
lean_inc(x_12);
x_119 = l_Lean_Syntax_node1(x_12, x_16, x_118);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_120 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_119, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_121 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_120, x_55);
lean_inc(x_12);
x_122 = l_Lean_Syntax_node1(x_12, x_16, x_121);
lean_inc(x_12);
x_123 = l_Lean_Syntax_node1(x_12, x_21, x_122);
lean_inc(x_12);
x_124 = l_Lean_Syntax_node1(x_12, x_20, x_123);
lean_inc_ref(x_24);
lean_inc(x_12);
x_125 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_124);
x_126 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__76);
x_127 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__78));
lean_inc(x_9);
lean_inc(x_8);
x_128 = l_Lean_addMacroScope(x_8, x_127, x_9);
x_129 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__80));
lean_inc(x_12);
x_130 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_130, 0, x_12);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set(x_130, 2, x_128);
lean_ctor_set(x_130, 3, x_129);
lean_inc_ref(x_30);
lean_inc(x_12);
x_131 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_130);
lean_inc(x_12);
x_132 = l_Lean_Syntax_node1(x_12, x_16, x_131);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_133 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_132, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_134 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_133, x_55);
lean_inc(x_12);
x_135 = l_Lean_Syntax_node1(x_12, x_16, x_134);
lean_inc(x_12);
x_136 = l_Lean_Syntax_node1(x_12, x_21, x_135);
lean_inc(x_12);
x_137 = l_Lean_Syntax_node1(x_12, x_20, x_136);
lean_inc_ref(x_24);
lean_inc(x_12);
x_138 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_137);
x_139 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__82);
x_140 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__84));
lean_inc(x_9);
lean_inc(x_8);
x_141 = l_Lean_addMacroScope(x_8, x_140, x_9);
x_142 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__86));
lean_inc(x_12);
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_12);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
lean_inc_ref(x_30);
lean_inc(x_12);
x_144 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_143);
lean_inc(x_12);
x_145 = l_Lean_Syntax_node1(x_12, x_16, x_144);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_146 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_145, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc_ref(x_27);
lean_inc(x_12);
x_147 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_146, x_55);
lean_inc(x_12);
x_148 = l_Lean_Syntax_node1(x_12, x_16, x_147);
lean_inc(x_12);
x_149 = l_Lean_Syntax_node1(x_12, x_21, x_148);
lean_inc(x_12);
x_150 = l_Lean_Syntax_node1(x_12, x_20, x_149);
lean_inc_ref(x_24);
lean_inc(x_12);
x_151 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_150);
x_152 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__88);
x_153 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__90));
lean_inc(x_9);
lean_inc(x_8);
x_154 = l_Lean_addMacroScope(x_8, x_153, x_9);
x_155 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__94));
lean_inc(x_12);
x_156 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_156, 0, x_12);
lean_ctor_set(x_156, 1, x_152);
lean_ctor_set(x_156, 2, x_154);
lean_ctor_set(x_156, 3, x_155);
lean_inc_ref(x_30);
lean_inc(x_12);
x_157 = l_Lean_Syntax_node2(x_12, x_35, x_30, x_156);
lean_inc(x_12);
x_158 = l_Lean_Syntax_node1(x_12, x_16, x_157);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_159 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_158, x_45);
lean_inc(x_55);
lean_inc(x_31);
lean_inc(x_12);
x_160 = l_Lean_Syntax_node4(x_12, x_25, x_27, x_31, x_159, x_55);
lean_inc(x_12);
x_161 = l_Lean_Syntax_node1(x_12, x_16, x_160);
lean_inc(x_12);
x_162 = l_Lean_Syntax_node1(x_12, x_21, x_161);
lean_inc(x_12);
x_163 = l_Lean_Syntax_node1(x_12, x_20, x_162);
lean_inc_ref(x_24);
lean_inc(x_12);
x_164 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_163);
x_165 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__95));
x_166 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__96));
lean_inc(x_12);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_12);
lean_ctor_set(x_167, 1, x_165);
x_168 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__98));
x_169 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__100));
x_170 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__101));
lean_inc(x_12);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_12);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__103);
x_173 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__104));
lean_inc(x_9);
lean_inc(x_8);
x_174 = l_Lean_addMacroScope(x_8, x_173, x_9);
lean_inc(x_12);
x_175 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_175, 0, x_12);
lean_ctor_set(x_175, 1, x_172);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_39);
lean_inc(x_12);
x_176 = l_Lean_Syntax_node2(x_12, x_169, x_171, x_175);
lean_inc(x_12);
x_177 = l_Lean_Syntax_node1(x_12, x_168, x_176);
lean_inc(x_12);
x_178 = l_Lean_Syntax_node1(x_12, x_16, x_177);
lean_inc(x_12);
x_179 = l_Lean_Syntax_node1(x_12, x_28, x_178);
x_180 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__105));
lean_inc(x_12);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_12);
lean_ctor_set(x_181, 1, x_180);
lean_inc(x_12);
x_182 = l_Lean_Syntax_node1(x_12, x_16, x_181);
x_183 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__107));
x_184 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__109);
x_185 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__112));
lean_inc(x_9);
lean_inc(x_8);
x_186 = l_Lean_addMacroScope(x_8, x_185, x_9);
x_187 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__114));
lean_inc(x_12);
x_188 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_188, 0, x_12);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_189 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_188);
lean_inc(x_12);
x_190 = l_Lean_Syntax_node1(x_12, x_16, x_189);
lean_inc_ref(x_45);
lean_inc_ref(x_34);
lean_inc(x_12);
x_191 = l_Lean_Syntax_node3(x_12, x_16, x_34, x_190, x_45);
lean_inc(x_182);
lean_inc_ref(x_30);
lean_inc(x_12);
x_192 = l_Lean_Syntax_node6(x_12, x_166, x_167, x_179, x_30, x_182, x_191, x_55);
lean_inc(x_12);
x_193 = l_Lean_Syntax_node1(x_12, x_16, x_192);
lean_inc(x_12);
x_194 = l_Lean_Syntax_node1(x_12, x_21, x_193);
lean_inc(x_12);
x_195 = l_Lean_Syntax_node1(x_12, x_20, x_194);
lean_inc_ref(x_24);
lean_inc(x_12);
x_196 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_195);
x_197 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__115));
x_198 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__116));
lean_inc(x_12);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_12);
lean_ctor_set(x_199, 1, x_197);
x_200 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__118);
x_201 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__121));
lean_inc(x_9);
lean_inc(x_8);
x_202 = l_Lean_addMacroScope(x_8, x_201, x_9);
x_203 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__123));
lean_inc(x_12);
x_204 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_204, 0, x_12);
lean_ctor_set(x_204, 1, x_200);
lean_ctor_set(x_204, 2, x_202);
lean_ctor_set(x_204, 3, x_203);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_205 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_204);
x_206 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__124));
lean_inc(x_12);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_12);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__126);
x_209 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__128));
lean_inc(x_9);
lean_inc(x_8);
x_210 = l_Lean_addMacroScope(x_8, x_209, x_9);
x_211 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__130));
lean_inc(x_12);
x_212 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_212, 0, x_12);
lean_ctor_set(x_212, 1, x_208);
lean_ctor_set(x_212, 2, x_210);
lean_ctor_set(x_212, 3, x_211);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_213 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_212);
x_214 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__132);
x_215 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__134));
lean_inc(x_9);
lean_inc(x_8);
x_216 = l_Lean_addMacroScope(x_8, x_215, x_9);
x_217 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__136));
lean_inc(x_12);
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_12);
lean_ctor_set(x_218, 1, x_214);
lean_ctor_set(x_218, 2, x_216);
lean_ctor_set(x_218, 3, x_217);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_219 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_218);
x_220 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__138);
x_221 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__140));
lean_inc(x_9);
lean_inc(x_8);
x_222 = l_Lean_addMacroScope(x_8, x_221, x_9);
x_223 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__142));
lean_inc(x_12);
x_224 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_224, 0, x_12);
lean_ctor_set(x_224, 1, x_220);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_223);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_225 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_224);
x_226 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__144);
x_227 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__146));
lean_inc(x_9);
lean_inc(x_8);
x_228 = l_Lean_addMacroScope(x_8, x_227, x_9);
x_229 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__148));
lean_inc(x_12);
x_230 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_230, 0, x_12);
lean_ctor_set(x_230, 1, x_226);
lean_ctor_set(x_230, 2, x_228);
lean_ctor_set(x_230, 3, x_229);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_231 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_230);
x_232 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__150);
x_233 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__152));
lean_inc(x_9);
lean_inc(x_8);
x_234 = l_Lean_addMacroScope(x_8, x_233, x_9);
x_235 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__154));
lean_inc(x_12);
x_236 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_236, 0, x_12);
lean_ctor_set(x_236, 1, x_232);
lean_ctor_set(x_236, 2, x_234);
lean_ctor_set(x_236, 3, x_235);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_237 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_236);
x_238 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__156);
x_239 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__158));
lean_inc(x_9);
lean_inc(x_8);
x_240 = l_Lean_addMacroScope(x_8, x_239, x_9);
x_241 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__160));
lean_inc(x_12);
x_242 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_242, 0, x_12);
lean_ctor_set(x_242, 1, x_238);
lean_ctor_set(x_242, 2, x_240);
lean_ctor_set(x_242, 3, x_241);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_243 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_242);
x_244 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__162);
x_245 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__164));
lean_inc(x_9);
lean_inc(x_8);
x_246 = l_Lean_addMacroScope(x_8, x_245, x_9);
x_247 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__166));
lean_inc(x_12);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_12);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_249 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_248);
x_250 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__168);
x_251 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__170));
x_252 = l_Lean_addMacroScope(x_8, x_251, x_9);
x_253 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__172));
lean_inc(x_12);
x_254 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_254, 0, x_12);
lean_ctor_set(x_254, 1, x_250);
lean_ctor_set(x_254, 2, x_252);
lean_ctor_set(x_254, 3, x_253);
lean_inc_ref_n(x_30, 2);
lean_inc(x_12);
x_255 = l_Lean_Syntax_node3(x_12, x_183, x_30, x_30, x_254);
x_256 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__173);
x_257 = lean_array_push(x_256, x_205);
lean_inc_ref(x_207);
x_258 = lean_array_push(x_257, x_207);
x_259 = lean_array_push(x_258, x_213);
lean_inc_ref(x_207);
x_260 = lean_array_push(x_259, x_207);
x_261 = lean_array_push(x_260, x_219);
lean_inc_ref(x_207);
x_262 = lean_array_push(x_261, x_207);
x_263 = lean_array_push(x_262, x_225);
lean_inc_ref(x_207);
x_264 = lean_array_push(x_263, x_207);
x_265 = lean_array_push(x_264, x_231);
lean_inc_ref(x_207);
x_266 = lean_array_push(x_265, x_207);
x_267 = lean_array_push(x_266, x_237);
lean_inc_ref(x_207);
x_268 = lean_array_push(x_267, x_207);
x_269 = lean_array_push(x_268, x_243);
lean_inc_ref(x_207);
x_270 = lean_array_push(x_269, x_207);
x_271 = lean_array_push(x_270, x_249);
x_272 = lean_array_push(x_271, x_207);
x_273 = lean_array_push(x_272, x_255);
lean_inc(x_12);
x_274 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_274, 0, x_12);
lean_ctor_set(x_274, 1, x_16);
lean_ctor_set(x_274, 2, x_273);
lean_inc(x_12);
x_275 = l_Lean_Syntax_node3(x_12, x_16, x_34, x_274, x_45);
lean_inc_ref_n(x_30, 2);
lean_inc(x_31);
lean_inc(x_12);
x_276 = l_Lean_Syntax_node6(x_12, x_198, x_199, x_31, x_30, x_182, x_275, x_30);
lean_inc(x_12);
x_277 = l_Lean_Syntax_node1(x_12, x_16, x_276);
lean_inc(x_12);
x_278 = l_Lean_Syntax_node1(x_12, x_21, x_277);
lean_inc(x_12);
x_279 = l_Lean_Syntax_node1(x_12, x_20, x_278);
lean_inc(x_12);
x_280 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_279);
x_281 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__174));
x_282 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__175));
lean_inc(x_12);
x_283 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_283, 0, x_12);
lean_ctor_set(x_283, 1, x_281);
lean_inc(x_12);
x_284 = l_Lean_Syntax_node2(x_12, x_282, x_283, x_31);
x_285 = lean_obj_once(&l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176, &l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176_once, _init_l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__176);
x_286 = lean_array_push(x_285, x_60);
lean_inc_ref(x_30);
x_287 = lean_array_push(x_286, x_30);
x_288 = lean_array_push(x_287, x_73);
lean_inc_ref(x_30);
x_289 = lean_array_push(x_288, x_30);
x_290 = lean_array_push(x_289, x_86);
lean_inc_ref(x_30);
x_291 = lean_array_push(x_290, x_30);
x_292 = lean_array_push(x_291, x_99);
lean_inc_ref(x_30);
x_293 = lean_array_push(x_292, x_30);
x_294 = lean_array_push(x_293, x_112);
lean_inc_ref(x_30);
x_295 = lean_array_push(x_294, x_30);
x_296 = lean_array_push(x_295, x_125);
lean_inc_ref(x_30);
x_297 = lean_array_push(x_296, x_30);
x_298 = lean_array_push(x_297, x_138);
lean_inc_ref(x_30);
x_299 = lean_array_push(x_298, x_30);
x_300 = lean_array_push(x_299, x_151);
lean_inc_ref(x_30);
x_301 = lean_array_push(x_300, x_30);
x_302 = lean_array_push(x_301, x_164);
lean_inc_ref(x_30);
x_303 = lean_array_push(x_302, x_30);
x_304 = lean_array_push(x_303, x_196);
lean_inc_ref(x_30);
x_305 = lean_array_push(x_304, x_30);
x_306 = lean_array_push(x_305, x_280);
x_307 = lean_array_push(x_306, x_30);
x_308 = lean_array_push(x_307, x_284);
lean_inc(x_12);
x_309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_309, 0, x_12);
lean_ctor_set(x_309, 1, x_16);
lean_ctor_set(x_309, 2, x_308);
lean_inc(x_12);
x_310 = l_Lean_Syntax_node1(x_12, x_21, x_309);
lean_inc(x_12);
x_311 = l_Lean_Syntax_node1(x_12, x_20, x_310);
lean_inc_ref(x_19);
lean_inc(x_12);
x_312 = l_Lean_Syntax_node2(x_12, x_17, x_19, x_311);
x_313 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__177));
x_314 = ((lean_object*)(l___aux__Init__Data__Range__Polymorphic__GetElemTactic______macroRules__tacticGet__elem__tactic__extensible__1___closed__178));
lean_inc(x_12);
x_315 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_315, 0, x_12);
lean_ctor_set(x_315, 1, x_313);
lean_inc(x_12);
x_316 = l_Lean_Syntax_node1(x_12, x_314, x_315);
lean_inc(x_12);
x_317 = l_Lean_Syntax_node1(x_12, x_16, x_316);
lean_inc(x_12);
x_318 = l_Lean_Syntax_node1(x_12, x_21, x_317);
lean_inc(x_12);
x_319 = l_Lean_Syntax_node1(x_12, x_20, x_318);
lean_inc(x_12);
x_320 = l_Lean_Syntax_node2(x_12, x_17, x_19, x_319);
lean_inc(x_12);
x_321 = l_Lean_Syntax_node2(x_12, x_16, x_312, x_320);
x_322 = l_Lean_Syntax_node2(x_12, x_14, x_15, x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_3);
return x_323;
}
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
