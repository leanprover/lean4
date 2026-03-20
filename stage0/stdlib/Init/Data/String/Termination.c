// Lean compiler output
// Module: Init.Data.String.Termination
// Imports: public import Init.Data.String.Lemmas.Splits public import Init.Data.String.FindPos import Init.Data.Option.Lemmas import Init.Omega import Init.ByCases import Init.Data.String.Lemmas.FindPos
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
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
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Slice"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value;
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Pos"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value;
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(173, 4, 120, 222, 71, 205, 160, 113)}};
static const lean_ctor_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value_aux_0),((lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(216, 52, 85, 20, 23, 200, 218, 224)}};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value;
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
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Slice.Pos.eq_prev_of_prev\?_eq_some"};
static const lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0 = (const lean_object*)&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0_value;
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes(lean_object* v_s_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_startInclusive_3_; lean_object* v_endExclusive_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_startInclusive_3_ = lean_ctor_get(v_s_1_, 1);
v_endExclusive_4_ = lean_ctor_get(v_s_1_, 2);
v___x_5_ = lean_nat_sub(v_endExclusive_4_, v_startInclusive_3_);
v___x_6_ = lean_nat_sub(v___x_5_, v_p_2_);
lean_dec(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes___boxed(lean_object* v_s_7_, lean_object* v_p_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_String_Slice_Pos_remainingBytes(v_s_7_, v_p_8_);
lean_dec(v_p_8_);
lean_dec_ref(v_s_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation(lean_object* v_s_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___boxed(lean_object* v_s_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_String_Slice_Pos_instWellFoundedRelation(v_s_12_);
lean_dec_ref(v_s_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg(lean_object* v_p_14_){
_start:
{
lean_inc(v_p_14_);
return v_p_14_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg___boxed(lean_object* v_p_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_String_Slice_Pos_down___redArg(v_p_15_);
lean_dec(v_p_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down(lean_object* v_s_17_, lean_object* v_p_18_){
_start:
{
lean_inc(v_p_18_);
return v_p_18_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___boxed(lean_object* v_s_19_, lean_object* v_p_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_String_Slice_Pos_down(v_s_19_, v_p_20_);
lean_dec(v_p_20_);
lean_dec_ref(v_s_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown(lean_object* v_s_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_box(0);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___boxed(lean_object* v_s_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_String_Slice_Pos_instWellFoundedRelationDown(v_s_24_);
lean_dec_ref(v_s_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes(lean_object* v_s_26_, lean_object* v_p_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_string_utf8_byte_size(v_s_26_);
v___x_30_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_30_, 0, v_s_26_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
v___x_31_ = l_String_Slice_Pos_remainingBytes(v___x_30_, v_p_27_);
lean_dec_ref(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes___boxed(lean_object* v_s_32_, lean_object* v_p_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_String_Pos_remainingBytes(v_s_32_, v_p_33_);
lean_dec(v_p_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation(lean_object* v_s_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___boxed(lean_object* v_s_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_String_Pos_instWellFoundedRelation(v_s_37_);
lean_dec_ref(v_s_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___redArg(lean_object* v_p_39_){
_start:
{
lean_inc(v_p_39_);
return v_p_39_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___redArg___boxed(lean_object* v_p_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_String_Pos_down___redArg(v_p_40_);
lean_dec(v_p_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down(lean_object* v_s_42_, lean_object* v_p_43_){
_start:
{
lean_inc(v_p_43_);
return v_p_43_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___boxed(lean_object* v_s_44_, lean_object* v_p_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_String_Pos_down(v_s_44_, v_p_45_);
lean_dec(v_p_45_);
lean_dec_ref(v_s_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown(lean_object* v_s_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___boxed(lean_object* v_s_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_String_Pos_instWellFoundedRelationDown(v_s_49_);
lean_dec_ref(v_s_49_);
return v_res_50_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30));
v___x_119_ = l_String_toRawSubstring_x27(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42));
v___x_144_ = l_String_toRawSubstring_x27(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Array_mkArray0(lean_box(0));
return v___x_167_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62));
v___x_189_ = l_String_toRawSubstring_x27(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_237_ = l_Lean_Syntax_isOfKind(v_x_233_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_a_234_);
v___x_238_ = lean_box(1);
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_a_235_);
return v___x_239_;
}
else
{
lean_object* v_quotContext_240_; lean_object* v_currMacroScope_241_; lean_object* v_ref_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_quotContext_240_ = lean_ctor_get(v_a_234_, 1);
lean_inc(v_quotContext_240_);
v_currMacroScope_241_ = lean_ctor_get(v_a_234_, 2);
lean_inc(v_currMacroScope_241_);
v_ref_242_ = lean_ctor_get(v_a_234_, 5);
lean_inc(v_ref_242_);
lean_dec_ref(v_a_234_);
v___x_243_ = 0;
v___x_244_ = l_Lean_SourceInfo_fromRef(v_ref_242_, v___x_243_);
lean_dec(v_ref_242_);
v___x_245_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_246_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_247_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(v___x_244_);
v___x_248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_244_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_250_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_251_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_252_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_253_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(v___x_244_);
v___x_254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_244_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_256_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(v___x_244_);
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_244_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
v___x_258_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_259_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_260_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_261_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_262_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_263_ = lean_box(0);
lean_inc(v_currMacroScope_241_);
lean_inc(v_quotContext_240_);
v___x_264_ = l_Lean_addMacroScope(v_quotContext_240_, v___x_263_, v_currMacroScope_241_);
v___x_265_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(v___x_244_);
v___x_266_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_266_, 0, v___x_244_);
lean_ctor_set(v___x_266_, 1, v___x_262_);
lean_ctor_set(v___x_266_, 2, v___x_264_);
lean_ctor_set(v___x_266_, 3, v___x_265_);
lean_inc(v___x_244_);
v___x_267_ = l_Lean_Syntax_node1(v___x_244_, v___x_261_, v___x_266_);
lean_inc_ref(v___x_248_);
lean_inc(v___x_244_);
v___x_268_ = l_Lean_Syntax_node2(v___x_244_, v___x_260_, v___x_248_, v___x_267_);
v___x_269_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_270_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_244_);
v___x_271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_244_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
lean_inc(v___x_244_);
v___x_272_ = l_Lean_Syntax_node1(v___x_244_, v___x_269_, v___x_271_);
v___x_273_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(v___x_244_);
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_244_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_276_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43);
v___x_277_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46));
lean_inc(v_currMacroScope_241_);
lean_inc(v_quotContext_240_);
v___x_278_ = l_Lean_addMacroScope(v_quotContext_240_, v___x_277_, v_currMacroScope_241_);
v___x_279_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51));
lean_inc(v___x_244_);
v___x_280_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_280_, 0, v___x_244_);
lean_ctor_set(v___x_280_, 1, v___x_276_);
lean_ctor_set(v___x_280_, 2, v___x_278_);
lean_ctor_set(v___x_280_, 3, v___x_279_);
lean_inc(v___x_272_);
lean_inc(v___x_244_);
v___x_281_ = l_Lean_Syntax_node1(v___x_244_, v___x_251_, v___x_272_);
lean_inc(v___x_244_);
v___x_282_ = l_Lean_Syntax_node2(v___x_244_, v___x_275_, v___x_280_, v___x_281_);
lean_inc(v___x_244_);
v___x_283_ = l_Lean_Syntax_node1(v___x_244_, v___x_251_, v___x_282_);
v___x_284_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(v___x_244_);
v___x_285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_244_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_inc_ref(v___x_285_);
lean_inc(v___x_272_);
lean_inc(v___x_268_);
lean_inc(v___x_244_);
v___x_286_ = l_Lean_Syntax_node5(v___x_244_, v___x_259_, v___x_268_, v___x_272_, v___x_274_, v___x_283_, v___x_285_);
v___x_287_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(v___x_244_);
v___x_288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_244_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
lean_inc(v___x_244_);
v___x_289_ = l_Lean_Syntax_node3(v___x_244_, v___x_258_, v___x_286_, v___x_288_, v___x_272_);
v___x_290_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
lean_inc(v___x_244_);
v___x_291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_291_, 0, v___x_244_);
lean_ctor_set(v___x_291_, 1, v___x_251_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
lean_inc_ref(v___x_291_);
lean_inc(v___x_244_);
v___x_292_ = l_Lean_Syntax_node3(v___x_244_, v___x_256_, v___x_257_, v___x_289_, v___x_291_);
lean_inc(v___x_244_);
v___x_293_ = l_Lean_Syntax_node1(v___x_244_, v___x_251_, v___x_292_);
lean_inc(v___x_244_);
v___x_294_ = l_Lean_Syntax_node1(v___x_244_, v___x_250_, v___x_293_);
lean_inc(v___x_244_);
v___x_295_ = l_Lean_Syntax_node1(v___x_244_, v___x_249_, v___x_294_);
lean_inc(v___x_244_);
v___x_296_ = l_Lean_Syntax_node2(v___x_244_, v___x_252_, v___x_254_, v___x_295_);
v___x_297_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_298_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(v___x_244_);
v___x_299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_244_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
v___x_300_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(v___x_291_);
lean_inc(v___x_244_);
v___x_301_ = l_Lean_Syntax_node1(v___x_244_, v___x_300_, v___x_291_);
v___x_302_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(v___x_244_);
v___x_303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_244_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_305_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63);
v___x_306_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65));
v___x_307_ = l_Lean_addMacroScope(v_quotContext_240_, v___x_306_, v_currMacroScope_241_);
v___x_308_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68));
lean_inc(v___x_244_);
v___x_309_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_309_, 0, v___x_244_);
lean_ctor_set(v___x_309_, 1, v___x_305_);
lean_ctor_set(v___x_309_, 2, v___x_307_);
lean_ctor_set(v___x_309_, 3, v___x_308_);
v___x_310_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_311_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_312_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(v___x_244_);
v___x_313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_244_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_315_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(v___x_244_);
v___x_316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_244_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_inc(v___x_244_);
v___x_317_ = l_Lean_Syntax_node1(v___x_244_, v___x_315_, v___x_316_);
lean_inc(v___x_244_);
v___x_318_ = l_Lean_Syntax_node1(v___x_244_, v___x_251_, v___x_317_);
lean_inc(v___x_244_);
v___x_319_ = l_Lean_Syntax_node1(v___x_244_, v___x_250_, v___x_318_);
lean_inc(v___x_244_);
v___x_320_ = l_Lean_Syntax_node1(v___x_244_, v___x_249_, v___x_319_);
lean_inc(v___x_244_);
v___x_321_ = l_Lean_Syntax_node2(v___x_244_, v___x_311_, v___x_313_, v___x_320_);
lean_inc_ref(v___x_285_);
lean_inc(v___x_244_);
v___x_322_ = l_Lean_Syntax_node3(v___x_244_, v___x_310_, v___x_268_, v___x_321_, v___x_285_);
lean_inc(v___x_244_);
v___x_323_ = l_Lean_Syntax_node1(v___x_244_, v___x_251_, v___x_322_);
lean_inc(v___x_244_);
v___x_324_ = l_Lean_Syntax_node2(v___x_244_, v___x_275_, v___x_309_, v___x_323_);
lean_inc_ref_n(v___x_291_, 2);
lean_inc(v___x_244_);
v___x_325_ = l_Lean_Syntax_node3(v___x_244_, v___x_304_, v___x_291_, v___x_291_, v___x_324_);
v___x_326_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(v___x_244_);
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_244_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
lean_inc(v___x_244_);
v___x_328_ = l_Lean_Syntax_node2(v___x_244_, v___x_251_, v___x_325_, v___x_327_);
v___x_329_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(v___x_244_);
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_244_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
lean_inc(v___x_244_);
v___x_331_ = l_Lean_Syntax_node3(v___x_244_, v___x_251_, v___x_303_, v___x_328_, v___x_330_);
lean_inc_ref_n(v___x_291_, 3);
lean_inc(v___x_244_);
v___x_332_ = l_Lean_Syntax_node6(v___x_244_, v___x_298_, v___x_299_, v___x_301_, v___x_291_, v___x_291_, v___x_331_, v___x_291_);
lean_inc(v___x_244_);
v___x_333_ = l_Lean_Syntax_node3(v___x_244_, v___x_251_, v___x_296_, v___x_291_, v___x_332_);
lean_inc(v___x_244_);
v___x_334_ = l_Lean_Syntax_node1(v___x_244_, v___x_250_, v___x_333_);
lean_inc(v___x_244_);
v___x_335_ = l_Lean_Syntax_node1(v___x_244_, v___x_249_, v___x_334_);
lean_inc(v___x_244_);
v___x_336_ = l_Lean_Syntax_node3(v___x_244_, v___x_246_, v___x_248_, v___x_335_, v___x_285_);
v___x_337_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(v___x_244_);
v___x_338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_244_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_340_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(v___x_244_);
v___x_341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_244_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_inc(v___x_244_);
v___x_342_ = l_Lean_Syntax_node1(v___x_244_, v___x_340_, v___x_341_);
v___x_343_ = l_Lean_Syntax_node3(v___x_244_, v___x_245_, v___x_336_, v___x_338_, v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_a_235_);
return v___x_344_;
}
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_347_ = l_String_toRawSubstring_x27(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_368_ = l_Lean_Syntax_isOfKind(v_x_364_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec_ref(v_a_365_);
v___x_369_ = lean_box(1);
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_a_366_);
return v___x_370_;
}
else
{
lean_object* v_quotContext_371_; lean_object* v_currMacroScope_372_; lean_object* v_ref_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_quotContext_371_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_quotContext_371_);
v_currMacroScope_372_ = lean_ctor_get(v_a_365_, 2);
lean_inc(v_currMacroScope_372_);
v_ref_373_ = lean_ctor_get(v_a_365_, 5);
lean_inc(v_ref_373_);
lean_dec_ref(v_a_365_);
v___x_374_ = 0;
v___x_375_ = l_Lean_SourceInfo_fromRef(v_ref_373_, v___x_374_);
lean_dec(v_ref_373_);
v___x_376_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_377_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_378_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(v___x_375_);
v___x_379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_375_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_381_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_382_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_383_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_384_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(v___x_375_);
v___x_385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_375_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_387_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(v___x_375_);
v___x_388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_375_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
v___x_389_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_390_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_391_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_392_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_393_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_394_ = lean_box(0);
lean_inc(v_currMacroScope_372_);
lean_inc(v_quotContext_371_);
v___x_395_ = l_Lean_addMacroScope(v_quotContext_371_, v___x_394_, v_currMacroScope_372_);
v___x_396_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(v___x_375_);
v___x_397_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_397_, 0, v___x_375_);
lean_ctor_set(v___x_397_, 1, v___x_393_);
lean_ctor_set(v___x_397_, 2, v___x_395_);
lean_ctor_set(v___x_397_, 3, v___x_396_);
lean_inc(v___x_375_);
v___x_398_ = l_Lean_Syntax_node1(v___x_375_, v___x_392_, v___x_397_);
lean_inc_ref(v___x_379_);
lean_inc(v___x_375_);
v___x_399_ = l_Lean_Syntax_node2(v___x_375_, v___x_391_, v___x_379_, v___x_398_);
v___x_400_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_401_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_375_);
v___x_402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_375_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
lean_inc(v___x_375_);
v___x_403_ = l_Lean_Syntax_node1(v___x_375_, v___x_400_, v___x_402_);
v___x_404_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(v___x_375_);
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_375_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_407_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43);
v___x_408_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46));
lean_inc(v_currMacroScope_372_);
lean_inc(v_quotContext_371_);
v___x_409_ = l_Lean_addMacroScope(v_quotContext_371_, v___x_408_, v_currMacroScope_372_);
v___x_410_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51));
lean_inc(v___x_375_);
v___x_411_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_411_, 0, v___x_375_);
lean_ctor_set(v___x_411_, 1, v___x_407_);
lean_ctor_set(v___x_411_, 2, v___x_409_);
lean_ctor_set(v___x_411_, 3, v___x_410_);
lean_inc(v___x_403_);
lean_inc(v___x_375_);
v___x_412_ = l_Lean_Syntax_node1(v___x_375_, v___x_382_, v___x_403_);
lean_inc(v___x_375_);
v___x_413_ = l_Lean_Syntax_node2(v___x_375_, v___x_406_, v___x_411_, v___x_412_);
lean_inc(v___x_375_);
v___x_414_ = l_Lean_Syntax_node1(v___x_375_, v___x_382_, v___x_413_);
v___x_415_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(v___x_375_);
v___x_416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_375_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
lean_inc_ref(v___x_416_);
lean_inc(v___x_403_);
lean_inc(v___x_399_);
lean_inc(v___x_375_);
v___x_417_ = l_Lean_Syntax_node5(v___x_375_, v___x_390_, v___x_399_, v___x_403_, v___x_405_, v___x_414_, v___x_416_);
v___x_418_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(v___x_375_);
v___x_419_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_375_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
lean_inc(v___x_375_);
v___x_420_ = l_Lean_Syntax_node3(v___x_375_, v___x_389_, v___x_417_, v___x_419_, v___x_403_);
v___x_421_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
lean_inc(v___x_375_);
v___x_422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_375_);
lean_ctor_set(v___x_422_, 1, v___x_382_);
lean_ctor_set(v___x_422_, 2, v___x_421_);
lean_inc_ref(v___x_422_);
lean_inc(v___x_375_);
v___x_423_ = l_Lean_Syntax_node3(v___x_375_, v___x_387_, v___x_388_, v___x_420_, v___x_422_);
lean_inc(v___x_375_);
v___x_424_ = l_Lean_Syntax_node1(v___x_375_, v___x_382_, v___x_423_);
lean_inc(v___x_375_);
v___x_425_ = l_Lean_Syntax_node1(v___x_375_, v___x_381_, v___x_424_);
lean_inc(v___x_375_);
v___x_426_ = l_Lean_Syntax_node1(v___x_375_, v___x_380_, v___x_425_);
lean_inc(v___x_375_);
v___x_427_ = l_Lean_Syntax_node2(v___x_375_, v___x_383_, v___x_385_, v___x_426_);
v___x_428_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_429_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(v___x_375_);
v___x_430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_375_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
v___x_431_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(v___x_422_);
lean_inc(v___x_375_);
v___x_432_ = l_Lean_Syntax_node1(v___x_375_, v___x_431_, v___x_422_);
v___x_433_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(v___x_375_);
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_375_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_436_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_437_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3));
v___x_438_ = l_Lean_addMacroScope(v_quotContext_371_, v___x_437_, v_currMacroScope_372_);
v___x_439_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6));
lean_inc(v___x_375_);
v___x_440_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_440_, 0, v___x_375_);
lean_ctor_set(v___x_440_, 1, v___x_436_);
lean_ctor_set(v___x_440_, 2, v___x_438_);
lean_ctor_set(v___x_440_, 3, v___x_439_);
v___x_441_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_442_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_443_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(v___x_375_);
v___x_444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_375_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_446_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(v___x_375_);
v___x_447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_375_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_inc(v___x_375_);
v___x_448_ = l_Lean_Syntax_node1(v___x_375_, v___x_446_, v___x_447_);
lean_inc(v___x_375_);
v___x_449_ = l_Lean_Syntax_node1(v___x_375_, v___x_382_, v___x_448_);
lean_inc(v___x_375_);
v___x_450_ = l_Lean_Syntax_node1(v___x_375_, v___x_381_, v___x_449_);
lean_inc(v___x_375_);
v___x_451_ = l_Lean_Syntax_node1(v___x_375_, v___x_380_, v___x_450_);
lean_inc(v___x_375_);
v___x_452_ = l_Lean_Syntax_node2(v___x_375_, v___x_442_, v___x_444_, v___x_451_);
lean_inc_ref(v___x_416_);
lean_inc(v___x_375_);
v___x_453_ = l_Lean_Syntax_node3(v___x_375_, v___x_441_, v___x_399_, v___x_452_, v___x_416_);
lean_inc(v___x_375_);
v___x_454_ = l_Lean_Syntax_node1(v___x_375_, v___x_382_, v___x_453_);
lean_inc(v___x_375_);
v___x_455_ = l_Lean_Syntax_node2(v___x_375_, v___x_406_, v___x_440_, v___x_454_);
lean_inc_ref_n(v___x_422_, 2);
lean_inc(v___x_375_);
v___x_456_ = l_Lean_Syntax_node3(v___x_375_, v___x_435_, v___x_422_, v___x_422_, v___x_455_);
v___x_457_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(v___x_375_);
v___x_458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_375_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
lean_inc(v___x_375_);
v___x_459_ = l_Lean_Syntax_node2(v___x_375_, v___x_382_, v___x_456_, v___x_458_);
v___x_460_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(v___x_375_);
v___x_461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_375_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
lean_inc(v___x_375_);
v___x_462_ = l_Lean_Syntax_node3(v___x_375_, v___x_382_, v___x_434_, v___x_459_, v___x_461_);
lean_inc_ref_n(v___x_422_, 3);
lean_inc(v___x_375_);
v___x_463_ = l_Lean_Syntax_node6(v___x_375_, v___x_429_, v___x_430_, v___x_432_, v___x_422_, v___x_422_, v___x_462_, v___x_422_);
lean_inc(v___x_375_);
v___x_464_ = l_Lean_Syntax_node3(v___x_375_, v___x_382_, v___x_427_, v___x_422_, v___x_463_);
lean_inc(v___x_375_);
v___x_465_ = l_Lean_Syntax_node1(v___x_375_, v___x_381_, v___x_464_);
lean_inc(v___x_375_);
v___x_466_ = l_Lean_Syntax_node1(v___x_375_, v___x_380_, v___x_465_);
lean_inc(v___x_375_);
v___x_467_ = l_Lean_Syntax_node3(v___x_375_, v___x_377_, v___x_379_, v___x_466_, v___x_416_);
v___x_468_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(v___x_375_);
v___x_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_375_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_471_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(v___x_375_);
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_375_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_inc(v___x_375_);
v___x_473_ = l_Lean_Syntax_node1(v___x_375_, v___x_471_, v___x_472_);
v___x_474_ = l_Lean_Syntax_node3(v___x_375_, v___x_376_, v___x_467_, v___x_469_, v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v_a_366_);
return v___x_475_;
}
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_478_ = l_String_toRawSubstring_x27(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7));
v___x_495_ = l_String_toRawSubstring_x27(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_513_ = l_Lean_Syntax_isOfKind(v_x_509_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref(v_a_510_);
v___x_514_ = lean_box(1);
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_a_511_);
return v___x_515_;
}
else
{
lean_object* v_quotContext_516_; lean_object* v_currMacroScope_517_; lean_object* v_ref_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_quotContext_516_ = lean_ctor_get(v_a_510_, 1);
lean_inc(v_quotContext_516_);
v_currMacroScope_517_ = lean_ctor_get(v_a_510_, 2);
lean_inc(v_currMacroScope_517_);
v_ref_518_ = lean_ctor_get(v_a_510_, 5);
lean_inc(v_ref_518_);
lean_dec_ref(v_a_510_);
v___x_519_ = 0;
v___x_520_ = l_Lean_SourceInfo_fromRef(v_ref_518_, v___x_519_);
lean_dec(v_ref_518_);
v___x_521_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_522_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_523_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(v___x_520_);
v___x_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_520_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_526_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_527_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_528_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_529_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(v___x_520_);
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_520_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_532_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(v___x_520_);
v___x_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_520_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
v___x_534_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_535_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_536_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_537_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_538_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_539_ = lean_box(0);
lean_inc(v_currMacroScope_517_);
lean_inc(v_quotContext_516_);
v___x_540_ = l_Lean_addMacroScope(v_quotContext_516_, v___x_539_, v_currMacroScope_517_);
v___x_541_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(v___x_520_);
v___x_542_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_542_, 0, v___x_520_);
lean_ctor_set(v___x_542_, 1, v___x_538_);
lean_ctor_set(v___x_542_, 2, v___x_540_);
lean_ctor_set(v___x_542_, 3, v___x_541_);
lean_inc(v___x_520_);
v___x_543_ = l_Lean_Syntax_node1(v___x_520_, v___x_537_, v___x_542_);
lean_inc_ref(v___x_524_);
lean_inc(v___x_520_);
v___x_544_ = l_Lean_Syntax_node2(v___x_520_, v___x_536_, v___x_524_, v___x_543_);
v___x_545_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_546_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_520_);
v___x_547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_520_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
lean_inc(v___x_520_);
v___x_548_ = l_Lean_Syntax_node1(v___x_520_, v___x_545_, v___x_547_);
v___x_549_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(v___x_520_);
v___x_550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_520_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_552_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_553_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2));
lean_inc(v_currMacroScope_517_);
lean_inc(v_quotContext_516_);
v___x_554_ = l_Lean_addMacroScope(v_quotContext_516_, v___x_553_, v_currMacroScope_517_);
v___x_555_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6));
lean_inc(v___x_520_);
v___x_556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_556_, 0, v___x_520_);
lean_ctor_set(v___x_556_, 1, v___x_552_);
lean_ctor_set(v___x_556_, 2, v___x_554_);
lean_ctor_set(v___x_556_, 3, v___x_555_);
lean_inc(v___x_548_);
lean_inc(v___x_520_);
v___x_557_ = l_Lean_Syntax_node1(v___x_520_, v___x_527_, v___x_548_);
lean_inc(v___x_520_);
v___x_558_ = l_Lean_Syntax_node2(v___x_520_, v___x_551_, v___x_556_, v___x_557_);
lean_inc(v___x_520_);
v___x_559_ = l_Lean_Syntax_node1(v___x_520_, v___x_527_, v___x_558_);
v___x_560_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(v___x_520_);
v___x_561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_520_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
lean_inc_ref(v___x_561_);
lean_inc(v___x_548_);
lean_inc(v___x_544_);
lean_inc(v___x_520_);
v___x_562_ = l_Lean_Syntax_node5(v___x_520_, v___x_535_, v___x_544_, v___x_548_, v___x_550_, v___x_559_, v___x_561_);
v___x_563_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(v___x_520_);
v___x_564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_520_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
lean_inc(v___x_520_);
v___x_565_ = l_Lean_Syntax_node3(v___x_520_, v___x_534_, v___x_562_, v___x_564_, v___x_548_);
v___x_566_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
lean_inc(v___x_520_);
v___x_567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_567_, 0, v___x_520_);
lean_ctor_set(v___x_567_, 1, v___x_527_);
lean_ctor_set(v___x_567_, 2, v___x_566_);
lean_inc_ref(v___x_567_);
lean_inc(v___x_520_);
v___x_568_ = l_Lean_Syntax_node3(v___x_520_, v___x_532_, v___x_533_, v___x_565_, v___x_567_);
lean_inc(v___x_520_);
v___x_569_ = l_Lean_Syntax_node1(v___x_520_, v___x_527_, v___x_568_);
lean_inc(v___x_520_);
v___x_570_ = l_Lean_Syntax_node1(v___x_520_, v___x_526_, v___x_569_);
lean_inc(v___x_520_);
v___x_571_ = l_Lean_Syntax_node1(v___x_520_, v___x_525_, v___x_570_);
lean_inc(v___x_520_);
v___x_572_ = l_Lean_Syntax_node2(v___x_520_, v___x_528_, v___x_530_, v___x_571_);
v___x_573_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_574_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(v___x_520_);
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_520_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
v___x_576_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(v___x_567_);
lean_inc(v___x_520_);
v___x_577_ = l_Lean_Syntax_node1(v___x_520_, v___x_576_, v___x_567_);
v___x_578_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(v___x_520_);
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_520_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_581_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8);
v___x_582_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9));
v___x_583_ = l_Lean_addMacroScope(v_quotContext_516_, v___x_582_, v_currMacroScope_517_);
v___x_584_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12));
lean_inc(v___x_520_);
v___x_585_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_585_, 0, v___x_520_);
lean_ctor_set(v___x_585_, 1, v___x_581_);
lean_ctor_set(v___x_585_, 2, v___x_583_);
lean_ctor_set(v___x_585_, 3, v___x_584_);
v___x_586_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_587_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_588_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(v___x_520_);
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_520_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_591_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(v___x_520_);
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_520_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_inc(v___x_520_);
v___x_593_ = l_Lean_Syntax_node1(v___x_520_, v___x_591_, v___x_592_);
lean_inc(v___x_520_);
v___x_594_ = l_Lean_Syntax_node1(v___x_520_, v___x_527_, v___x_593_);
lean_inc(v___x_520_);
v___x_595_ = l_Lean_Syntax_node1(v___x_520_, v___x_526_, v___x_594_);
lean_inc(v___x_520_);
v___x_596_ = l_Lean_Syntax_node1(v___x_520_, v___x_525_, v___x_595_);
lean_inc(v___x_520_);
v___x_597_ = l_Lean_Syntax_node2(v___x_520_, v___x_587_, v___x_589_, v___x_596_);
lean_inc_ref(v___x_561_);
lean_inc(v___x_520_);
v___x_598_ = l_Lean_Syntax_node3(v___x_520_, v___x_586_, v___x_544_, v___x_597_, v___x_561_);
lean_inc(v___x_520_);
v___x_599_ = l_Lean_Syntax_node1(v___x_520_, v___x_527_, v___x_598_);
lean_inc(v___x_520_);
v___x_600_ = l_Lean_Syntax_node2(v___x_520_, v___x_551_, v___x_585_, v___x_599_);
lean_inc_ref_n(v___x_567_, 2);
lean_inc(v___x_520_);
v___x_601_ = l_Lean_Syntax_node3(v___x_520_, v___x_580_, v___x_567_, v___x_567_, v___x_600_);
v___x_602_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(v___x_520_);
v___x_603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_520_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_inc(v___x_520_);
v___x_604_ = l_Lean_Syntax_node2(v___x_520_, v___x_527_, v___x_601_, v___x_603_);
v___x_605_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(v___x_520_);
v___x_606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_520_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
lean_inc(v___x_520_);
v___x_607_ = l_Lean_Syntax_node3(v___x_520_, v___x_527_, v___x_579_, v___x_604_, v___x_606_);
lean_inc_ref_n(v___x_567_, 3);
lean_inc(v___x_520_);
v___x_608_ = l_Lean_Syntax_node6(v___x_520_, v___x_574_, v___x_575_, v___x_577_, v___x_567_, v___x_567_, v___x_607_, v___x_567_);
lean_inc(v___x_520_);
v___x_609_ = l_Lean_Syntax_node3(v___x_520_, v___x_527_, v___x_572_, v___x_567_, v___x_608_);
lean_inc(v___x_520_);
v___x_610_ = l_Lean_Syntax_node1(v___x_520_, v___x_526_, v___x_609_);
lean_inc(v___x_520_);
v___x_611_ = l_Lean_Syntax_node1(v___x_520_, v___x_525_, v___x_610_);
lean_inc(v___x_520_);
v___x_612_ = l_Lean_Syntax_node3(v___x_520_, v___x_522_, v___x_524_, v___x_611_, v___x_561_);
v___x_613_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(v___x_520_);
v___x_614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_520_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_616_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(v___x_520_);
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_520_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_inc(v___x_520_);
v___x_618_ = l_Lean_Syntax_node1(v___x_520_, v___x_616_, v___x_617_);
v___x_619_ = l_Lean_Syntax_node3(v___x_520_, v___x_521_, v___x_612_, v___x_614_, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_a_511_);
return v___x_620_;
}
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0));
v___x_623_ = l_String_toRawSubstring_x27(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4(lean_object* v_x_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_641_ = l_Lean_Syntax_isOfKind(v_x_637_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref(v_a_638_);
v___x_642_ = lean_box(1);
v___x_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_a_639_);
return v___x_643_;
}
else
{
lean_object* v_quotContext_644_; lean_object* v_currMacroScope_645_; lean_object* v_ref_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_quotContext_644_ = lean_ctor_get(v_a_638_, 1);
lean_inc(v_quotContext_644_);
v_currMacroScope_645_ = lean_ctor_get(v_a_638_, 2);
lean_inc(v_currMacroScope_645_);
v_ref_646_ = lean_ctor_get(v_a_638_, 5);
lean_inc(v_ref_646_);
lean_dec_ref(v_a_638_);
v___x_647_ = 0;
v___x_648_ = l_Lean_SourceInfo_fromRef(v_ref_646_, v___x_647_);
lean_dec(v_ref_646_);
v___x_649_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_650_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_651_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc(v___x_648_);
v___x_652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_648_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_654_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_655_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_656_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_657_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
lean_inc(v___x_648_);
v___x_658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_648_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_660_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
lean_inc(v___x_648_);
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_648_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
v___x_662_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_663_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_664_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_665_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_666_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_667_ = lean_box(0);
lean_inc(v_currMacroScope_645_);
lean_inc(v_quotContext_644_);
v___x_668_ = l_Lean_addMacroScope(v_quotContext_644_, v___x_667_, v_currMacroScope_645_);
v___x_669_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
lean_inc(v___x_648_);
v___x_670_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_670_, 0, v___x_648_);
lean_ctor_set(v___x_670_, 1, v___x_666_);
lean_ctor_set(v___x_670_, 2, v___x_668_);
lean_ctor_set(v___x_670_, 3, v___x_669_);
lean_inc(v___x_648_);
v___x_671_ = l_Lean_Syntax_node1(v___x_648_, v___x_665_, v___x_670_);
lean_inc_ref(v___x_652_);
lean_inc(v___x_648_);
v___x_672_ = l_Lean_Syntax_node2(v___x_648_, v___x_664_, v___x_652_, v___x_671_);
v___x_673_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_674_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_648_);
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_648_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
lean_inc(v___x_648_);
v___x_676_ = l_Lean_Syntax_node1(v___x_648_, v___x_673_, v___x_675_);
v___x_677_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
lean_inc(v___x_648_);
v___x_678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_648_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_680_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_681_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2));
lean_inc(v_currMacroScope_645_);
lean_inc(v_quotContext_644_);
v___x_682_ = l_Lean_addMacroScope(v_quotContext_644_, v___x_681_, v_currMacroScope_645_);
v___x_683_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6));
lean_inc(v___x_648_);
v___x_684_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_684_, 0, v___x_648_);
lean_ctor_set(v___x_684_, 1, v___x_680_);
lean_ctor_set(v___x_684_, 2, v___x_682_);
lean_ctor_set(v___x_684_, 3, v___x_683_);
lean_inc(v___x_676_);
lean_inc(v___x_648_);
v___x_685_ = l_Lean_Syntax_node1(v___x_648_, v___x_655_, v___x_676_);
lean_inc(v___x_648_);
v___x_686_ = l_Lean_Syntax_node2(v___x_648_, v___x_679_, v___x_684_, v___x_685_);
lean_inc(v___x_648_);
v___x_687_ = l_Lean_Syntax_node1(v___x_648_, v___x_655_, v___x_686_);
v___x_688_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
lean_inc(v___x_648_);
v___x_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_648_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
lean_inc_ref(v___x_689_);
lean_inc(v___x_676_);
lean_inc(v___x_672_);
lean_inc(v___x_648_);
v___x_690_ = l_Lean_Syntax_node5(v___x_648_, v___x_663_, v___x_672_, v___x_676_, v___x_678_, v___x_687_, v___x_689_);
v___x_691_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
lean_inc(v___x_648_);
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_648_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
lean_inc(v___x_648_);
v___x_693_ = l_Lean_Syntax_node3(v___x_648_, v___x_662_, v___x_690_, v___x_692_, v___x_676_);
v___x_694_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
lean_inc(v___x_648_);
v___x_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_695_, 0, v___x_648_);
lean_ctor_set(v___x_695_, 1, v___x_655_);
lean_ctor_set(v___x_695_, 2, v___x_694_);
lean_inc_ref(v___x_695_);
lean_inc(v___x_648_);
v___x_696_ = l_Lean_Syntax_node3(v___x_648_, v___x_660_, v___x_661_, v___x_693_, v___x_695_);
lean_inc(v___x_648_);
v___x_697_ = l_Lean_Syntax_node1(v___x_648_, v___x_655_, v___x_696_);
lean_inc(v___x_648_);
v___x_698_ = l_Lean_Syntax_node1(v___x_648_, v___x_654_, v___x_697_);
lean_inc(v___x_648_);
v___x_699_ = l_Lean_Syntax_node1(v___x_648_, v___x_653_, v___x_698_);
lean_inc(v___x_648_);
v___x_700_ = l_Lean_Syntax_node2(v___x_648_, v___x_656_, v___x_658_, v___x_699_);
v___x_701_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_702_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
lean_inc(v___x_648_);
v___x_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_648_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
v___x_704_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
lean_inc_ref(v___x_695_);
lean_inc(v___x_648_);
v___x_705_ = l_Lean_Syntax_node1(v___x_648_, v___x_704_, v___x_695_);
v___x_706_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
lean_inc(v___x_648_);
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_648_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_709_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1);
v___x_710_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2));
v___x_711_ = l_Lean_addMacroScope(v_quotContext_644_, v___x_710_, v_currMacroScope_645_);
v___x_712_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5));
lean_inc(v___x_648_);
v___x_713_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_713_, 0, v___x_648_);
lean_ctor_set(v___x_713_, 1, v___x_709_);
lean_ctor_set(v___x_713_, 2, v___x_711_);
lean_ctor_set(v___x_713_, 3, v___x_712_);
v___x_714_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_715_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_716_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
lean_inc(v___x_648_);
v___x_717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_648_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_719_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
lean_inc(v___x_648_);
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_648_);
lean_ctor_set(v___x_720_, 1, v___x_718_);
lean_inc(v___x_648_);
v___x_721_ = l_Lean_Syntax_node1(v___x_648_, v___x_719_, v___x_720_);
lean_inc(v___x_648_);
v___x_722_ = l_Lean_Syntax_node1(v___x_648_, v___x_655_, v___x_721_);
lean_inc(v___x_648_);
v___x_723_ = l_Lean_Syntax_node1(v___x_648_, v___x_654_, v___x_722_);
lean_inc(v___x_648_);
v___x_724_ = l_Lean_Syntax_node1(v___x_648_, v___x_653_, v___x_723_);
lean_inc(v___x_648_);
v___x_725_ = l_Lean_Syntax_node2(v___x_648_, v___x_715_, v___x_717_, v___x_724_);
lean_inc_ref(v___x_689_);
lean_inc(v___x_648_);
v___x_726_ = l_Lean_Syntax_node3(v___x_648_, v___x_714_, v___x_672_, v___x_725_, v___x_689_);
lean_inc(v___x_648_);
v___x_727_ = l_Lean_Syntax_node1(v___x_648_, v___x_655_, v___x_726_);
lean_inc(v___x_648_);
v___x_728_ = l_Lean_Syntax_node2(v___x_648_, v___x_679_, v___x_713_, v___x_727_);
lean_inc_ref_n(v___x_695_, 2);
lean_inc(v___x_648_);
v___x_729_ = l_Lean_Syntax_node3(v___x_648_, v___x_708_, v___x_695_, v___x_695_, v___x_728_);
v___x_730_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
lean_inc(v___x_648_);
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_648_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_inc(v___x_648_);
v___x_732_ = l_Lean_Syntax_node2(v___x_648_, v___x_655_, v___x_729_, v___x_731_);
v___x_733_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
lean_inc(v___x_648_);
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_648_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
lean_inc(v___x_648_);
v___x_735_ = l_Lean_Syntax_node3(v___x_648_, v___x_655_, v___x_707_, v___x_732_, v___x_734_);
lean_inc_ref_n(v___x_695_, 3);
lean_inc(v___x_648_);
v___x_736_ = l_Lean_Syntax_node6(v___x_648_, v___x_702_, v___x_703_, v___x_705_, v___x_695_, v___x_695_, v___x_735_, v___x_695_);
lean_inc(v___x_648_);
v___x_737_ = l_Lean_Syntax_node3(v___x_648_, v___x_655_, v___x_700_, v___x_695_, v___x_736_);
lean_inc(v___x_648_);
v___x_738_ = l_Lean_Syntax_node1(v___x_648_, v___x_654_, v___x_737_);
lean_inc(v___x_648_);
v___x_739_ = l_Lean_Syntax_node1(v___x_648_, v___x_653_, v___x_738_);
lean_inc(v___x_648_);
v___x_740_ = l_Lean_Syntax_node3(v___x_648_, v___x_650_, v___x_652_, v___x_739_, v___x_689_);
v___x_741_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
lean_inc(v___x_648_);
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_648_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_744_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
lean_inc(v___x_648_);
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_648_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
lean_inc(v___x_648_);
v___x_746_ = l_Lean_Syntax_node1(v___x_648_, v___x_744_, v___x_745_);
v___x_747_ = l_Lean_Syntax_node3(v___x_648_, v___x_649_, v___x_740_, v___x_742_, v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_a_639_);
return v___x_748_;
}
}
}
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Termination(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Termination(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Termination(builtin);
}
#ifdef __cplusplus
}
#endif
