// Lean compiler output
// Module: Init.Data.String.Termination
// Imports: public import Init.Data.String.Lemmas.Splits import Init.Data.Option.Lemmas import Init.Omega
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___boxed(lean_object*);
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "tacticDecreasing_trivial"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 154, 34, 2, 43, 185, 79)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(228, 221, 63, 213, 180, 29, 27, 230)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33_value)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Slice.Pos"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42_value;
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Slice"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Pos"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(173, 4, 120, 222, 71, 205, 160, 113)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(216, 52, 85, 20, 23, 200, 218, 224)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(84, 178, 198, 6, 19, 246, 168, 69)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(21, 101, 147, 105, 116, 117, 171, 195)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48_value),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50_value)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Slice.Pos.eq_next_of_next\?_eq_some"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62_value;
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_next_of_next\?_eq_some"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(173, 4, 120, 222, 71, 205, 160, 113)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(216, 52, 85, 20, 23, 200, 218, 224)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(34, 42, 77, 134, 100, 32, 215, 189)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(84, 178, 198, 6, 19, 246, 168, 69)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(21, 101, 147, 105, 116, 117, 171, 195)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(35, 24, 123, 185, 27, 23, 37, 33)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Slice.Pos.eq_prev_of_prev\?_eq_some"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0_value;
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_prev_of_prev\?_eq_some"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(173, 4, 120, 222, 71, 205, 160, 113)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(216, 52, 85, 20, 23, 200, 218, 224)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 93, 236, 157, 92, 179, 239, 42)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(84, 178, 198, 6, 19, 246, 168, 69)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(21, 101, 147, 105, 116, 117, 171, 195)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 201, 255, 187, 150, 12, 196, 200)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6_value;
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "String.Pos"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0_value;
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3_value),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5_value)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Pos.eq_next_of_next\?_eq_some"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7_value;
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 182, 83, 236, 144, 113, 47)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(20, 112, 8, 106, 214, 219, 166, 165)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(145, 7, 53, 187, 7, 187, 52, 250)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12_value;
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Pos.eq_prev_of_prev\?_eq_some"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0_value;
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 182, 83, 236, 144, 113, 47)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(26, 162, 51, 32, 164, 165, 227, 217)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(23, 199, 94, 93, 229, 180, 38, 14)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5_value;
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_sub(x_4, x_3);
x_6 = lean_nat_sub(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_remainingBytes(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_instWellFoundedRelation(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_down___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_down(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_instWellFoundedRelationDown(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_remainingBytes(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_remainingBytes(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_instWellFoundedRelation(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_down___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_down(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_instWellFoundedRelationDown(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
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
x_13 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
x_14 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
x_15 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
x_18 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
x_19 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
x_20 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
x_21 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(x_12);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
x_24 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_23);
x_26 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
x_27 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
x_28 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
x_29 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
x_30 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31;
x_31 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_32 = l_Lean_addMacroScope(x_8, x_31, x_9);
x_33 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(x_12);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_12);
x_35 = l_Lean_Syntax_node1(x_12, x_29, x_34);
lean_inc_ref(x_16);
lean_inc(x_12);
x_36 = l_Lean_Syntax_node2(x_12, x_28, x_16, x_35);
x_37 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
x_38 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(x_12);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node1(x_12, x_37, x_39);
x_41 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(x_12);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
x_44 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43;
x_45 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46));
lean_inc(x_9);
lean_inc(x_8);
x_46 = l_Lean_addMacroScope(x_8, x_45, x_9);
x_47 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51));
lean_inc(x_12);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
lean_inc(x_40);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_19, x_40);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node2(x_12, x_43, x_48, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_19, x_50);
x_52 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(x_12);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
lean_inc_ref(x_53);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_12);
x_54 = l_Lean_Syntax_node5(x_12, x_27, x_36, x_40, x_42, x_51, x_53);
x_55 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(x_12);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node3(x_12, x_26, x_54, x_56, x_40);
x_58 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54;
lean_inc(x_12);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_19);
lean_ctor_set(x_59, 2, x_58);
lean_inc_ref(x_59);
lean_inc(x_12);
x_60 = l_Lean_Syntax_node3(x_12, x_24, x_25, x_57, x_59);
lean_inc(x_12);
x_61 = l_Lean_Syntax_node1(x_12, x_19, x_60);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node1(x_12, x_18, x_61);
lean_inc(x_12);
x_63 = l_Lean_Syntax_node1(x_12, x_17, x_62);
lean_inc(x_12);
x_64 = l_Lean_Syntax_node2(x_12, x_20, x_22, x_63);
x_65 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
x_66 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(x_12);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_65);
x_68 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(x_59);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node1(x_12, x_68, x_59);
x_70 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(x_12);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_12);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
x_73 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63;
x_74 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65));
x_75 = l_Lean_addMacroScope(x_8, x_74, x_9);
x_76 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68));
lean_inc(x_12);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_76);
x_78 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
x_79 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
x_80 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(x_12);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_81, 1, x_80);
x_82 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
x_83 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(x_12);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_82);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node1(x_12, x_83, x_84);
lean_inc(x_12);
x_86 = l_Lean_Syntax_node1(x_12, x_19, x_85);
lean_inc(x_12);
x_87 = l_Lean_Syntax_node1(x_12, x_18, x_86);
lean_inc(x_12);
x_88 = l_Lean_Syntax_node1(x_12, x_17, x_87);
lean_inc(x_12);
x_89 = l_Lean_Syntax_node2(x_12, x_79, x_81, x_88);
lean_inc_ref(x_53);
lean_inc(x_12);
x_90 = l_Lean_Syntax_node3(x_12, x_78, x_36, x_89, x_53);
lean_inc(x_12);
x_91 = l_Lean_Syntax_node1(x_12, x_19, x_90);
lean_inc(x_12);
x_92 = l_Lean_Syntax_node2(x_12, x_43, x_77, x_91);
lean_inc_ref_n(x_59, 2);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node3(x_12, x_72, x_59, x_59, x_92);
x_94 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(x_12);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_12);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node2(x_12, x_19, x_93, x_95);
x_97 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(x_12);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_12);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_12);
x_99 = l_Lean_Syntax_node3(x_12, x_19, x_71, x_96, x_98);
lean_inc_ref_n(x_59, 3);
lean_inc(x_12);
x_100 = l_Lean_Syntax_node6(x_12, x_66, x_67, x_69, x_59, x_59, x_99, x_59);
lean_inc(x_12);
x_101 = l_Lean_Syntax_node3(x_12, x_19, x_64, x_59, x_100);
lean_inc(x_12);
x_102 = l_Lean_Syntax_node1(x_12, x_18, x_101);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node1(x_12, x_17, x_102);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node3(x_12, x_14, x_16, x_103, x_53);
x_105 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(x_12);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_12);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
x_108 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(x_12);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_107);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node1(x_12, x_108, x_109);
x_111 = l_Lean_Syntax_node3(x_12, x_13, x_104, x_106, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
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
x_13 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
x_14 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
x_15 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
x_18 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
x_19 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
x_20 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
x_21 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(x_12);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
x_24 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_23);
x_26 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
x_27 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
x_28 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
x_29 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
x_30 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31;
x_31 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_32 = l_Lean_addMacroScope(x_8, x_31, x_9);
x_33 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(x_12);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_12);
x_35 = l_Lean_Syntax_node1(x_12, x_29, x_34);
lean_inc_ref(x_16);
lean_inc(x_12);
x_36 = l_Lean_Syntax_node2(x_12, x_28, x_16, x_35);
x_37 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
x_38 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(x_12);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node1(x_12, x_37, x_39);
x_41 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(x_12);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
x_44 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43;
x_45 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46));
lean_inc(x_9);
lean_inc(x_8);
x_46 = l_Lean_addMacroScope(x_8, x_45, x_9);
x_47 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51));
lean_inc(x_12);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
lean_inc(x_40);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_19, x_40);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node2(x_12, x_43, x_48, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_19, x_50);
x_52 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(x_12);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
lean_inc_ref(x_53);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_12);
x_54 = l_Lean_Syntax_node5(x_12, x_27, x_36, x_40, x_42, x_51, x_53);
x_55 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(x_12);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node3(x_12, x_26, x_54, x_56, x_40);
x_58 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54;
lean_inc(x_12);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_19);
lean_ctor_set(x_59, 2, x_58);
lean_inc_ref(x_59);
lean_inc(x_12);
x_60 = l_Lean_Syntax_node3(x_12, x_24, x_25, x_57, x_59);
lean_inc(x_12);
x_61 = l_Lean_Syntax_node1(x_12, x_19, x_60);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node1(x_12, x_18, x_61);
lean_inc(x_12);
x_63 = l_Lean_Syntax_node1(x_12, x_17, x_62);
lean_inc(x_12);
x_64 = l_Lean_Syntax_node2(x_12, x_20, x_22, x_63);
x_65 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
x_66 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(x_12);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_65);
x_68 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(x_59);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node1(x_12, x_68, x_59);
x_70 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(x_12);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_12);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
x_73 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1;
x_74 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3));
x_75 = l_Lean_addMacroScope(x_8, x_74, x_9);
x_76 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6));
lean_inc(x_12);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_76);
x_78 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
x_79 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
x_80 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(x_12);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_81, 1, x_80);
x_82 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
x_83 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(x_12);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_82);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node1(x_12, x_83, x_84);
lean_inc(x_12);
x_86 = l_Lean_Syntax_node1(x_12, x_19, x_85);
lean_inc(x_12);
x_87 = l_Lean_Syntax_node1(x_12, x_18, x_86);
lean_inc(x_12);
x_88 = l_Lean_Syntax_node1(x_12, x_17, x_87);
lean_inc(x_12);
x_89 = l_Lean_Syntax_node2(x_12, x_79, x_81, x_88);
lean_inc_ref(x_53);
lean_inc(x_12);
x_90 = l_Lean_Syntax_node3(x_12, x_78, x_36, x_89, x_53);
lean_inc(x_12);
x_91 = l_Lean_Syntax_node1(x_12, x_19, x_90);
lean_inc(x_12);
x_92 = l_Lean_Syntax_node2(x_12, x_43, x_77, x_91);
lean_inc_ref_n(x_59, 2);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node3(x_12, x_72, x_59, x_59, x_92);
x_94 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(x_12);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_12);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node2(x_12, x_19, x_93, x_95);
x_97 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(x_12);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_12);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_12);
x_99 = l_Lean_Syntax_node3(x_12, x_19, x_71, x_96, x_98);
lean_inc_ref_n(x_59, 3);
lean_inc(x_12);
x_100 = l_Lean_Syntax_node6(x_12, x_66, x_67, x_69, x_59, x_59, x_99, x_59);
lean_inc(x_12);
x_101 = l_Lean_Syntax_node3(x_12, x_19, x_64, x_59, x_100);
lean_inc(x_12);
x_102 = l_Lean_Syntax_node1(x_12, x_18, x_101);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node1(x_12, x_17, x_102);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node3(x_12, x_14, x_16, x_103, x_53);
x_105 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(x_12);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_12);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
x_108 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(x_12);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_107);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node1(x_12, x_108, x_109);
x_111 = l_Lean_Syntax_node3(x_12, x_13, x_104, x_106, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
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
x_13 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
x_14 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
x_15 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
x_18 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
x_19 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
x_20 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
x_21 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(x_12);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
x_24 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_23);
x_26 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
x_27 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
x_28 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
x_29 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
x_30 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31;
x_31 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_32 = l_Lean_addMacroScope(x_8, x_31, x_9);
x_33 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(x_12);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_12);
x_35 = l_Lean_Syntax_node1(x_12, x_29, x_34);
lean_inc_ref(x_16);
lean_inc(x_12);
x_36 = l_Lean_Syntax_node2(x_12, x_28, x_16, x_35);
x_37 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
x_38 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(x_12);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node1(x_12, x_37, x_39);
x_41 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(x_12);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
x_44 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1;
x_45 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2));
lean_inc(x_9);
lean_inc(x_8);
x_46 = l_Lean_addMacroScope(x_8, x_45, x_9);
x_47 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6));
lean_inc(x_12);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
lean_inc(x_40);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_19, x_40);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node2(x_12, x_43, x_48, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_19, x_50);
x_52 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(x_12);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
lean_inc_ref(x_53);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_12);
x_54 = l_Lean_Syntax_node5(x_12, x_27, x_36, x_40, x_42, x_51, x_53);
x_55 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(x_12);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node3(x_12, x_26, x_54, x_56, x_40);
x_58 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54;
lean_inc(x_12);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_19);
lean_ctor_set(x_59, 2, x_58);
lean_inc_ref(x_59);
lean_inc(x_12);
x_60 = l_Lean_Syntax_node3(x_12, x_24, x_25, x_57, x_59);
lean_inc(x_12);
x_61 = l_Lean_Syntax_node1(x_12, x_19, x_60);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node1(x_12, x_18, x_61);
lean_inc(x_12);
x_63 = l_Lean_Syntax_node1(x_12, x_17, x_62);
lean_inc(x_12);
x_64 = l_Lean_Syntax_node2(x_12, x_20, x_22, x_63);
x_65 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
x_66 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(x_12);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_65);
x_68 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(x_59);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node1(x_12, x_68, x_59);
x_70 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(x_12);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_12);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
x_73 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8;
x_74 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9));
x_75 = l_Lean_addMacroScope(x_8, x_74, x_9);
x_76 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12));
lean_inc(x_12);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_76);
x_78 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
x_79 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
x_80 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(x_12);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_81, 1, x_80);
x_82 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
x_83 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(x_12);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_82);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node1(x_12, x_83, x_84);
lean_inc(x_12);
x_86 = l_Lean_Syntax_node1(x_12, x_19, x_85);
lean_inc(x_12);
x_87 = l_Lean_Syntax_node1(x_12, x_18, x_86);
lean_inc(x_12);
x_88 = l_Lean_Syntax_node1(x_12, x_17, x_87);
lean_inc(x_12);
x_89 = l_Lean_Syntax_node2(x_12, x_79, x_81, x_88);
lean_inc_ref(x_53);
lean_inc(x_12);
x_90 = l_Lean_Syntax_node3(x_12, x_78, x_36, x_89, x_53);
lean_inc(x_12);
x_91 = l_Lean_Syntax_node1(x_12, x_19, x_90);
lean_inc(x_12);
x_92 = l_Lean_Syntax_node2(x_12, x_43, x_77, x_91);
lean_inc_ref_n(x_59, 2);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node3(x_12, x_72, x_59, x_59, x_92);
x_94 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(x_12);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_12);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node2(x_12, x_19, x_93, x_95);
x_97 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(x_12);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_12);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_12);
x_99 = l_Lean_Syntax_node3(x_12, x_19, x_71, x_96, x_98);
lean_inc_ref_n(x_59, 3);
lean_inc(x_12);
x_100 = l_Lean_Syntax_node6(x_12, x_66, x_67, x_69, x_59, x_59, x_99, x_59);
lean_inc(x_12);
x_101 = l_Lean_Syntax_node3(x_12, x_19, x_64, x_59, x_100);
lean_inc(x_12);
x_102 = l_Lean_Syntax_node1(x_12, x_18, x_101);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node1(x_12, x_17, x_102);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node3(x_12, x_14, x_16, x_103, x_53);
x_105 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(x_12);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_12);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
x_108 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(x_12);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_107);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node1(x_12, x_108, x_109);
x_111 = l_Lean_Syntax_node3(x_12, x_13, x_104, x_106, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
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
x_13 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
x_14 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
x_15 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
x_18 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
x_19 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
x_20 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
x_21 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(x_12);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
x_24 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_23);
x_26 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
x_27 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
x_28 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
x_29 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
x_30 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31;
x_31 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_32 = l_Lean_addMacroScope(x_8, x_31, x_9);
x_33 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(x_12);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_12);
x_35 = l_Lean_Syntax_node1(x_12, x_29, x_34);
lean_inc_ref(x_16);
lean_inc(x_12);
x_36 = l_Lean_Syntax_node2(x_12, x_28, x_16, x_35);
x_37 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
x_38 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(x_12);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node1(x_12, x_37, x_39);
x_41 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(x_12);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
x_44 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1;
x_45 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2));
lean_inc(x_9);
lean_inc(x_8);
x_46 = l_Lean_addMacroScope(x_8, x_45, x_9);
x_47 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6));
lean_inc(x_12);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
lean_inc(x_40);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_19, x_40);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node2(x_12, x_43, x_48, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_19, x_50);
x_52 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(x_12);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
lean_inc_ref(x_53);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_12);
x_54 = l_Lean_Syntax_node5(x_12, x_27, x_36, x_40, x_42, x_51, x_53);
x_55 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(x_12);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node3(x_12, x_26, x_54, x_56, x_40);
x_58 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54;
lean_inc(x_12);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_19);
lean_ctor_set(x_59, 2, x_58);
lean_inc_ref(x_59);
lean_inc(x_12);
x_60 = l_Lean_Syntax_node3(x_12, x_24, x_25, x_57, x_59);
lean_inc(x_12);
x_61 = l_Lean_Syntax_node1(x_12, x_19, x_60);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node1(x_12, x_18, x_61);
lean_inc(x_12);
x_63 = l_Lean_Syntax_node1(x_12, x_17, x_62);
lean_inc(x_12);
x_64 = l_Lean_Syntax_node2(x_12, x_20, x_22, x_63);
x_65 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
x_66 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(x_12);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_65);
x_68 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(x_59);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node1(x_12, x_68, x_59);
x_70 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(x_12);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_12);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
x_73 = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1;
x_74 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2));
x_75 = l_Lean_addMacroScope(x_8, x_74, x_9);
x_76 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5));
lean_inc(x_12);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_76);
x_78 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
x_79 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
x_80 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(x_12);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_81, 1, x_80);
x_82 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
x_83 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(x_12);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_82);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node1(x_12, x_83, x_84);
lean_inc(x_12);
x_86 = l_Lean_Syntax_node1(x_12, x_19, x_85);
lean_inc(x_12);
x_87 = l_Lean_Syntax_node1(x_12, x_18, x_86);
lean_inc(x_12);
x_88 = l_Lean_Syntax_node1(x_12, x_17, x_87);
lean_inc(x_12);
x_89 = l_Lean_Syntax_node2(x_12, x_79, x_81, x_88);
lean_inc_ref(x_53);
lean_inc(x_12);
x_90 = l_Lean_Syntax_node3(x_12, x_78, x_36, x_89, x_53);
lean_inc(x_12);
x_91 = l_Lean_Syntax_node1(x_12, x_19, x_90);
lean_inc(x_12);
x_92 = l_Lean_Syntax_node2(x_12, x_43, x_77, x_91);
lean_inc_ref_n(x_59, 2);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node3(x_12, x_72, x_59, x_59, x_92);
x_94 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(x_12);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_12);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node2(x_12, x_19, x_93, x_95);
x_97 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(x_12);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_12);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_12);
x_99 = l_Lean_Syntax_node3(x_12, x_19, x_71, x_96, x_98);
lean_inc_ref_n(x_59, 3);
lean_inc(x_12);
x_100 = l_Lean_Syntax_node6(x_12, x_66, x_67, x_69, x_59, x_59, x_99, x_59);
lean_inc(x_12);
x_101 = l_Lean_Syntax_node3(x_12, x_19, x_64, x_59, x_100);
lean_inc(x_12);
x_102 = l_Lean_Syntax_node1(x_12, x_18, x_101);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node1(x_12, x_17, x_102);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node3(x_12, x_14, x_16, x_103, x_53);
x_105 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(x_12);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_12);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
x_108 = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(x_12);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_107);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node1(x_12, x_108, x_109);
x_111 = l_Lean_Syntax_node3(x_12, x_13, x_104, x_106, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
}
}
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Termination(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8);
l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1 = _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1();
lean_mark_persistent(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
