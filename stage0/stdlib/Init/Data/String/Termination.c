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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_remainingBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___redArg();
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_down___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___redArg();
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_String_Slice_Pos_instWellFoundedRelation___redArg();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation(lean_object* v_s_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelation___boxed(lean_object* v_s_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_String_Slice_Pos_instWellFoundedRelation(v_s_16_);
lean_dec_ref(v_s_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg(lean_object* v_p_18_){
_start:
{
lean_inc(v_p_18_);
return v_p_18_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___redArg___boxed(lean_object* v_p_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_String_Slice_Pos_down___redArg(v_p_19_);
lean_dec(v_p_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down(lean_object* v_s_21_, lean_object* v_p_22_){
_start:
{
lean_inc(v_p_22_);
return v_p_22_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_down___boxed(lean_object* v_s_23_, lean_object* v_p_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_String_Slice_Pos_down(v_s_23_, v_p_24_);
lean_dec(v_p_24_);
lean_dec_ref(v_s_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___redArg(){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_String_Slice_Pos_instWellFoundedRelationDown___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown(lean_object* v_s_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instWellFoundedRelationDown___boxed(lean_object* v_s_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_String_Slice_Pos_instWellFoundedRelationDown(v_s_32_);
lean_dec_ref(v_s_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes(lean_object* v_s_34_, lean_object* v_p_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_string_utf8_byte_size(v_s_34_);
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v_s_34_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_37_);
v___x_39_ = l_String_Slice_Pos_remainingBytes(v___x_38_, v_p_35_);
lean_dec_ref_known(v___x_38_, 3);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_remainingBytes___boxed(lean_object* v_s_40_, lean_object* v_p_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_String_Pos_remainingBytes(v_s_40_, v_p_41_);
lean_dec(v_p_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_String_Pos_instWellFoundedRelation___redArg();
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation(lean_object* v_s_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelation___boxed(lean_object* v_s_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_String_Pos_instWellFoundedRelation(v_s_49_);
lean_dec_ref(v_s_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___redArg(lean_object* v_p_51_){
_start:
{
lean_inc(v_p_51_);
return v_p_51_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___redArg___boxed(lean_object* v_p_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_String_Pos_down___redArg(v_p_52_);
lean_dec(v_p_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down(lean_object* v_s_54_, lean_object* v_p_55_){
_start:
{
lean_inc(v_p_55_);
return v_p_55_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_down___boxed(lean_object* v_s_56_, lean_object* v_p_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_String_Pos_down(v_s_56_, v_p_57_);
lean_dec(v_p_57_);
lean_dec_ref(v_s_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___redArg(){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_box(0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___redArg___boxed(lean_object* v___dummy_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_String_Pos_instWellFoundedRelationDown___redArg();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown(lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instWellFoundedRelationDown___boxed(lean_object* v_s_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_Pos_instWellFoundedRelationDown(v_s_65_);
lean_dec_ref(v_s_65_);
return v_res_66_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30));
v___x_135_ = l_String_toRawSubstring_x27(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42));
v___x_160_ = l_String_toRawSubstring_x27(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Array_mkArray0___redArg();
return v___x_183_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62));
v___x_205_ = l_String_toRawSubstring_x27(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_253_ = l_Lean_Syntax_isOfKind(v_x_249_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(1);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_251_);
return v___x_255_;
}
else
{
lean_object* v_quotContext_256_; lean_object* v_currMacroScope_257_; lean_object* v_ref_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_quotContext_256_ = lean_ctor_get(v_a_250_, 1);
v_currMacroScope_257_ = lean_ctor_get(v_a_250_, 2);
v_ref_258_ = lean_ctor_get(v_a_250_, 5);
v___x_259_ = 0;
v___x_260_ = l_Lean_SourceInfo_fromRef(v_ref_258_, v___x_259_);
v___x_261_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_262_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_263_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc_n(v___x_260_, 50);
v___x_264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_260_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_266_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_267_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_268_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_269_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
v___x_270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_260_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_272_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_260_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
v___x_274_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_275_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_276_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_277_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_278_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_279_ = lean_box(0);
lean_inc_n(v_currMacroScope_257_, 3);
lean_inc_n(v_quotContext_256_, 3);
v___x_280_ = l_Lean_addMacroScope(v_quotContext_256_, v___x_279_, v_currMacroScope_257_);
v___x_281_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
v___x_282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_282_, 0, v___x_260_);
lean_ctor_set(v___x_282_, 1, v___x_278_);
lean_ctor_set(v___x_282_, 2, v___x_280_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
v___x_283_ = l_Lean_Syntax_node1(v___x_260_, v___x_277_, v___x_282_);
lean_inc_ref(v___x_264_);
v___x_284_ = l_Lean_Syntax_node2(v___x_260_, v___x_276_, v___x_264_, v___x_283_);
v___x_285_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_286_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_260_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Lean_Syntax_node1(v___x_260_, v___x_285_, v___x_287_);
v___x_289_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_260_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_292_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43);
v___x_293_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_294_ = l_Lean_addMacroScope(v_quotContext_256_, v___x_293_, v_currMacroScope_257_);
v___x_295_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51));
v___x_296_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_296_, 0, v___x_260_);
lean_ctor_set(v___x_296_, 1, v___x_292_);
lean_ctor_set(v___x_296_, 2, v___x_294_);
lean_ctor_set(v___x_296_, 3, v___x_295_);
lean_inc_n(v___x_288_, 2);
v___x_297_ = l_Lean_Syntax_node1(v___x_260_, v___x_267_, v___x_288_);
v___x_298_ = l_Lean_Syntax_node2(v___x_260_, v___x_291_, v___x_296_, v___x_297_);
v___x_299_ = l_Lean_Syntax_node1(v___x_260_, v___x_267_, v___x_298_);
v___x_300_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
v___x_301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_260_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
lean_inc_ref_n(v___x_301_, 2);
lean_inc(v___x_284_);
v___x_302_ = l_Lean_Syntax_node5(v___x_260_, v___x_275_, v___x_284_, v___x_288_, v___x_290_, v___x_299_, v___x_301_);
v___x_303_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
v___x_304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_260_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_Syntax_node3(v___x_260_, v___x_274_, v___x_302_, v___x_304_, v___x_288_);
v___x_306_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
v___x_307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_307_, 0, v___x_260_);
lean_ctor_set(v___x_307_, 1, v___x_267_);
lean_ctor_set(v___x_307_, 2, v___x_306_);
lean_inc_ref_n(v___x_307_, 7);
v___x_308_ = l_Lean_Syntax_node3(v___x_260_, v___x_272_, v___x_273_, v___x_305_, v___x_307_);
v___x_309_ = l_Lean_Syntax_node1(v___x_260_, v___x_267_, v___x_308_);
v___x_310_ = l_Lean_Syntax_node1(v___x_260_, v___x_266_, v___x_309_);
v___x_311_ = l_Lean_Syntax_node1(v___x_260_, v___x_265_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node2(v___x_260_, v___x_268_, v___x_270_, v___x_311_);
v___x_313_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_314_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
v___x_315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_260_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
v___x_316_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
v___x_317_ = l_Lean_Syntax_node1(v___x_260_, v___x_316_, v___x_307_);
v___x_318_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_260_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_321_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63);
v___x_322_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65));
v___x_323_ = l_Lean_addMacroScope(v_quotContext_256_, v___x_322_, v_currMacroScope_257_);
v___x_324_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68));
v___x_325_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_325_, 0, v___x_260_);
lean_ctor_set(v___x_325_, 1, v___x_321_);
lean_ctor_set(v___x_325_, 2, v___x_323_);
lean_ctor_set(v___x_325_, 3, v___x_324_);
v___x_326_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_327_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_328_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
v___x_329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_260_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_331_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
v___x_332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_260_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
v___x_333_ = l_Lean_Syntax_node1(v___x_260_, v___x_331_, v___x_332_);
v___x_334_ = l_Lean_Syntax_node1(v___x_260_, v___x_267_, v___x_333_);
v___x_335_ = l_Lean_Syntax_node1(v___x_260_, v___x_266_, v___x_334_);
v___x_336_ = l_Lean_Syntax_node1(v___x_260_, v___x_265_, v___x_335_);
v___x_337_ = l_Lean_Syntax_node2(v___x_260_, v___x_327_, v___x_329_, v___x_336_);
v___x_338_ = l_Lean_Syntax_node3(v___x_260_, v___x_326_, v___x_284_, v___x_337_, v___x_301_);
v___x_339_ = l_Lean_Syntax_node1(v___x_260_, v___x_267_, v___x_338_);
v___x_340_ = l_Lean_Syntax_node2(v___x_260_, v___x_291_, v___x_325_, v___x_339_);
v___x_341_ = l_Lean_Syntax_node3(v___x_260_, v___x_320_, v___x_307_, v___x_307_, v___x_340_);
v___x_342_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_260_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_Lean_Syntax_node2(v___x_260_, v___x_267_, v___x_341_, v___x_343_);
v___x_345_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
v___x_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_260_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_Syntax_node3(v___x_260_, v___x_267_, v___x_319_, v___x_344_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node6(v___x_260_, v___x_314_, v___x_315_, v___x_317_, v___x_307_, v___x_307_, v___x_347_, v___x_307_);
v___x_349_ = l_Lean_Syntax_node3(v___x_260_, v___x_267_, v___x_312_, v___x_307_, v___x_348_);
v___x_350_ = l_Lean_Syntax_node1(v___x_260_, v___x_266_, v___x_349_);
v___x_351_ = l_Lean_Syntax_node1(v___x_260_, v___x_265_, v___x_350_);
v___x_352_ = l_Lean_Syntax_node3(v___x_260_, v___x_262_, v___x_264_, v___x_351_, v___x_301_);
v___x_353_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_260_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_356_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
v___x_357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_260_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
v___x_358_ = l_Lean_Syntax_node1(v___x_260_, v___x_356_, v___x_357_);
v___x_359_ = l_Lean_Syntax_node3(v___x_260_, v___x_261_, v___x_352_, v___x_354_, v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v_a_251_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(v_x_361_, v_a_362_, v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_364_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_367_ = l_String_toRawSubstring_x27(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_388_ = l_Lean_Syntax_isOfKind(v_x_384_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_box(1);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_a_386_);
return v___x_390_;
}
else
{
lean_object* v_quotContext_391_; lean_object* v_currMacroScope_392_; lean_object* v_ref_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_quotContext_391_ = lean_ctor_get(v_a_385_, 1);
v_currMacroScope_392_ = lean_ctor_get(v_a_385_, 2);
v_ref_393_ = lean_ctor_get(v_a_385_, 5);
v___x_394_ = 0;
v___x_395_ = l_Lean_SourceInfo_fromRef(v_ref_393_, v___x_394_);
v___x_396_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_397_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_398_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc_n(v___x_395_, 50);
v___x_399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_395_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_401_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_402_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_403_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_404_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_395_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_407_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_395_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
v___x_409_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_410_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_411_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_412_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_413_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_414_ = lean_box(0);
lean_inc_n(v_currMacroScope_392_, 3);
lean_inc_n(v_quotContext_391_, 3);
v___x_415_ = l_Lean_addMacroScope(v_quotContext_391_, v___x_414_, v_currMacroScope_392_);
v___x_416_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
v___x_417_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_417_, 0, v___x_395_);
lean_ctor_set(v___x_417_, 1, v___x_413_);
lean_ctor_set(v___x_417_, 2, v___x_415_);
lean_ctor_set(v___x_417_, 3, v___x_416_);
v___x_418_ = l_Lean_Syntax_node1(v___x_395_, v___x_412_, v___x_417_);
lean_inc_ref(v___x_399_);
v___x_419_ = l_Lean_Syntax_node2(v___x_395_, v___x_411_, v___x_399_, v___x_418_);
v___x_420_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_421_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_395_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_Syntax_node1(v___x_395_, v___x_420_, v___x_422_);
v___x_424_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_395_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_427_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43);
v___x_428_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_429_ = l_Lean_addMacroScope(v_quotContext_391_, v___x_428_, v_currMacroScope_392_);
v___x_430_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51));
v___x_431_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_431_, 0, v___x_395_);
lean_ctor_set(v___x_431_, 1, v___x_427_);
lean_ctor_set(v___x_431_, 2, v___x_429_);
lean_ctor_set(v___x_431_, 3, v___x_430_);
lean_inc_n(v___x_423_, 2);
v___x_432_ = l_Lean_Syntax_node1(v___x_395_, v___x_402_, v___x_423_);
v___x_433_ = l_Lean_Syntax_node2(v___x_395_, v___x_426_, v___x_431_, v___x_432_);
v___x_434_ = l_Lean_Syntax_node1(v___x_395_, v___x_402_, v___x_433_);
v___x_435_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
v___x_436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_395_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
lean_inc_ref_n(v___x_436_, 2);
lean_inc(v___x_419_);
v___x_437_ = l_Lean_Syntax_node5(v___x_395_, v___x_410_, v___x_419_, v___x_423_, v___x_425_, v___x_434_, v___x_436_);
v___x_438_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
v___x_439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_395_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_Syntax_node3(v___x_395_, v___x_409_, v___x_437_, v___x_439_, v___x_423_);
v___x_441_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
v___x_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_395_);
lean_ctor_set(v___x_442_, 1, v___x_402_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
lean_inc_ref_n(v___x_442_, 7);
v___x_443_ = l_Lean_Syntax_node3(v___x_395_, v___x_407_, v___x_408_, v___x_440_, v___x_442_);
v___x_444_ = l_Lean_Syntax_node1(v___x_395_, v___x_402_, v___x_443_);
v___x_445_ = l_Lean_Syntax_node1(v___x_395_, v___x_401_, v___x_444_);
v___x_446_ = l_Lean_Syntax_node1(v___x_395_, v___x_400_, v___x_445_);
v___x_447_ = l_Lean_Syntax_node2(v___x_395_, v___x_403_, v___x_405_, v___x_446_);
v___x_448_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_449_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
v___x_450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_395_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
v___x_451_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
v___x_452_ = l_Lean_Syntax_node1(v___x_395_, v___x_451_, v___x_442_);
v___x_453_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
v___x_454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_395_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_456_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_457_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3));
v___x_458_ = l_Lean_addMacroScope(v_quotContext_391_, v___x_457_, v_currMacroScope_392_);
v___x_459_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6));
v___x_460_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_460_, 0, v___x_395_);
lean_ctor_set(v___x_460_, 1, v___x_456_);
lean_ctor_set(v___x_460_, 2, v___x_458_);
lean_ctor_set(v___x_460_, 3, v___x_459_);
v___x_461_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_462_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_463_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_395_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_466_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
v___x_467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_395_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
v___x_468_ = l_Lean_Syntax_node1(v___x_395_, v___x_466_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_395_, v___x_402_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node1(v___x_395_, v___x_401_, v___x_469_);
v___x_471_ = l_Lean_Syntax_node1(v___x_395_, v___x_400_, v___x_470_);
v___x_472_ = l_Lean_Syntax_node2(v___x_395_, v___x_462_, v___x_464_, v___x_471_);
v___x_473_ = l_Lean_Syntax_node3(v___x_395_, v___x_461_, v___x_419_, v___x_472_, v___x_436_);
v___x_474_ = l_Lean_Syntax_node1(v___x_395_, v___x_402_, v___x_473_);
v___x_475_ = l_Lean_Syntax_node2(v___x_395_, v___x_426_, v___x_460_, v___x_474_);
v___x_476_ = l_Lean_Syntax_node3(v___x_395_, v___x_455_, v___x_442_, v___x_442_, v___x_475_);
v___x_477_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
v___x_478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_395_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_Syntax_node2(v___x_395_, v___x_402_, v___x_476_, v___x_478_);
v___x_480_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
v___x_481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_395_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Lean_Syntax_node3(v___x_395_, v___x_402_, v___x_454_, v___x_479_, v___x_481_);
v___x_483_ = l_Lean_Syntax_node6(v___x_395_, v___x_449_, v___x_450_, v___x_452_, v___x_442_, v___x_442_, v___x_482_, v___x_442_);
v___x_484_ = l_Lean_Syntax_node3(v___x_395_, v___x_402_, v___x_447_, v___x_442_, v___x_483_);
v___x_485_ = l_Lean_Syntax_node1(v___x_395_, v___x_401_, v___x_484_);
v___x_486_ = l_Lean_Syntax_node1(v___x_395_, v___x_400_, v___x_485_);
v___x_487_ = l_Lean_Syntax_node3(v___x_395_, v___x_397_, v___x_399_, v___x_486_, v___x_436_);
v___x_488_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
v___x_489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_395_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_491_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
v___x_492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_395_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
v___x_493_ = l_Lean_Syntax_node1(v___x_395_, v___x_491_, v___x_492_);
v___x_494_ = l_Lean_Syntax_node3(v___x_395_, v___x_396_, v___x_487_, v___x_489_, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_a_386_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2(v_x_496_, v_a_497_, v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_499_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_502_ = l_String_toRawSubstring_x27(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7));
v___x_519_ = l_String_toRawSubstring_x27(v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_537_ = l_Lean_Syntax_isOfKind(v_x_533_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_box(1);
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_a_535_);
return v___x_539_;
}
else
{
lean_object* v_quotContext_540_; lean_object* v_currMacroScope_541_; lean_object* v_ref_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_quotContext_540_ = lean_ctor_get(v_a_534_, 1);
v_currMacroScope_541_ = lean_ctor_get(v_a_534_, 2);
v_ref_542_ = lean_ctor_get(v_a_534_, 5);
v___x_543_ = 0;
v___x_544_ = l_Lean_SourceInfo_fromRef(v_ref_542_, v___x_543_);
v___x_545_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_546_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_547_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc_n(v___x_544_, 50);
v___x_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_544_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_550_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_551_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_552_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_553_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
v___x_554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_544_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_556_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_544_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
v___x_558_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_559_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_560_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_561_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_562_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_563_ = lean_box(0);
lean_inc_n(v_currMacroScope_541_, 3);
lean_inc_n(v_quotContext_540_, 3);
v___x_564_ = l_Lean_addMacroScope(v_quotContext_540_, v___x_563_, v_currMacroScope_541_);
v___x_565_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
v___x_566_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_566_, 0, v___x_544_);
lean_ctor_set(v___x_566_, 1, v___x_562_);
lean_ctor_set(v___x_566_, 2, v___x_564_);
lean_ctor_set(v___x_566_, 3, v___x_565_);
v___x_567_ = l_Lean_Syntax_node1(v___x_544_, v___x_561_, v___x_566_);
lean_inc_ref(v___x_548_);
v___x_568_ = l_Lean_Syntax_node2(v___x_544_, v___x_560_, v___x_548_, v___x_567_);
v___x_569_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_570_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_544_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_Syntax_node1(v___x_544_, v___x_569_, v___x_571_);
v___x_573_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_544_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_576_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_577_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2));
v___x_578_ = l_Lean_addMacroScope(v_quotContext_540_, v___x_577_, v_currMacroScope_541_);
v___x_579_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6));
v___x_580_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_580_, 0, v___x_544_);
lean_ctor_set(v___x_580_, 1, v___x_576_);
lean_ctor_set(v___x_580_, 2, v___x_578_);
lean_ctor_set(v___x_580_, 3, v___x_579_);
lean_inc_n(v___x_572_, 2);
v___x_581_ = l_Lean_Syntax_node1(v___x_544_, v___x_551_, v___x_572_);
v___x_582_ = l_Lean_Syntax_node2(v___x_544_, v___x_575_, v___x_580_, v___x_581_);
v___x_583_ = l_Lean_Syntax_node1(v___x_544_, v___x_551_, v___x_582_);
v___x_584_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_544_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
lean_inc_ref_n(v___x_585_, 2);
lean_inc(v___x_568_);
v___x_586_ = l_Lean_Syntax_node5(v___x_544_, v___x_559_, v___x_568_, v___x_572_, v___x_574_, v___x_583_, v___x_585_);
v___x_587_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
v___x_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_544_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_Syntax_node3(v___x_544_, v___x_558_, v___x_586_, v___x_588_, v___x_572_);
v___x_590_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
v___x_591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_591_, 0, v___x_544_);
lean_ctor_set(v___x_591_, 1, v___x_551_);
lean_ctor_set(v___x_591_, 2, v___x_590_);
lean_inc_ref_n(v___x_591_, 7);
v___x_592_ = l_Lean_Syntax_node3(v___x_544_, v___x_556_, v___x_557_, v___x_589_, v___x_591_);
v___x_593_ = l_Lean_Syntax_node1(v___x_544_, v___x_551_, v___x_592_);
v___x_594_ = l_Lean_Syntax_node1(v___x_544_, v___x_550_, v___x_593_);
v___x_595_ = l_Lean_Syntax_node1(v___x_544_, v___x_549_, v___x_594_);
v___x_596_ = l_Lean_Syntax_node2(v___x_544_, v___x_552_, v___x_554_, v___x_595_);
v___x_597_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_598_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
v___x_599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_544_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
v___x_600_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
v___x_601_ = l_Lean_Syntax_node1(v___x_544_, v___x_600_, v___x_591_);
v___x_602_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
v___x_603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_544_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_605_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8);
v___x_606_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9));
v___x_607_ = l_Lean_addMacroScope(v_quotContext_540_, v___x_606_, v_currMacroScope_541_);
v___x_608_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12));
v___x_609_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_609_, 0, v___x_544_);
lean_ctor_set(v___x_609_, 1, v___x_605_);
lean_ctor_set(v___x_609_, 2, v___x_607_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
v___x_610_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_611_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_612_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
v___x_613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_544_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_615_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
v___x_616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_544_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
v___x_617_ = l_Lean_Syntax_node1(v___x_544_, v___x_615_, v___x_616_);
v___x_618_ = l_Lean_Syntax_node1(v___x_544_, v___x_551_, v___x_617_);
v___x_619_ = l_Lean_Syntax_node1(v___x_544_, v___x_550_, v___x_618_);
v___x_620_ = l_Lean_Syntax_node1(v___x_544_, v___x_549_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node2(v___x_544_, v___x_611_, v___x_613_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node3(v___x_544_, v___x_610_, v___x_568_, v___x_621_, v___x_585_);
v___x_623_ = l_Lean_Syntax_node1(v___x_544_, v___x_551_, v___x_622_);
v___x_624_ = l_Lean_Syntax_node2(v___x_544_, v___x_575_, v___x_609_, v___x_623_);
v___x_625_ = l_Lean_Syntax_node3(v___x_544_, v___x_604_, v___x_591_, v___x_591_, v___x_624_);
v___x_626_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
v___x_627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_544_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Lean_Syntax_node2(v___x_544_, v___x_551_, v___x_625_, v___x_627_);
v___x_629_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
v___x_630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_544_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_Syntax_node3(v___x_544_, v___x_551_, v___x_603_, v___x_628_, v___x_630_);
v___x_632_ = l_Lean_Syntax_node6(v___x_544_, v___x_598_, v___x_599_, v___x_601_, v___x_591_, v___x_591_, v___x_631_, v___x_591_);
v___x_633_ = l_Lean_Syntax_node3(v___x_544_, v___x_551_, v___x_596_, v___x_591_, v___x_632_);
v___x_634_ = l_Lean_Syntax_node1(v___x_544_, v___x_550_, v___x_633_);
v___x_635_ = l_Lean_Syntax_node1(v___x_544_, v___x_549_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node3(v___x_544_, v___x_546_, v___x_548_, v___x_635_, v___x_585_);
v___x_637_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
v___x_638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_544_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_640_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
v___x_641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_544_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
v___x_642_ = l_Lean_Syntax_node1(v___x_544_, v___x_640_, v___x_641_);
v___x_643_ = l_Lean_Syntax_node3(v___x_544_, v___x_545_, v___x_636_, v___x_638_, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_a_535_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* v_x_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3(v_x_645_, v_a_646_, v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_648_;
}
}
static lean_object* _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0));
v___x_651_ = l_String_toRawSubstring_x27(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4(lean_object* v_x_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_669_ = l_Lean_Syntax_isOfKind(v_x_665_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(1);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_a_667_);
return v___x_671_;
}
else
{
lean_object* v_quotContext_672_; lean_object* v_currMacroScope_673_; lean_object* v_ref_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_quotContext_672_ = lean_ctor_get(v_a_666_, 1);
v_currMacroScope_673_ = lean_ctor_get(v_a_666_, 2);
v_ref_674_ = lean_ctor_get(v_a_666_, 5);
v___x_675_ = 0;
v___x_676_ = l_Lean_SourceInfo_fromRef(v_ref_674_, v___x_675_);
v___x_677_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_678_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_679_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9));
lean_inc_n(v___x_676_, 50);
v___x_680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_676_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_682_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_683_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_684_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_685_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18));
v___x_686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_676_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19));
v___x_688_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_676_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
v___x_690_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_691_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_692_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_693_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29));
v___x_694_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
v___x_695_ = lean_box(0);
lean_inc_n(v_currMacroScope_673_, 3);
lean_inc_n(v_quotContext_672_, 3);
v___x_696_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_695_, v_currMacroScope_673_);
v___x_697_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35));
v___x_698_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_698_, 0, v___x_676_);
lean_ctor_set(v___x_698_, 1, v___x_694_);
lean_ctor_set(v___x_698_, 2, v___x_696_);
lean_ctor_set(v___x_698_, 3, v___x_697_);
v___x_699_ = l_Lean_Syntax_node1(v___x_676_, v___x_693_, v___x_698_);
lean_inc_ref(v___x_680_);
v___x_700_ = l_Lean_Syntax_node2(v___x_676_, v___x_692_, v___x_680_, v___x_699_);
v___x_701_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_702_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_676_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Lean_Syntax_node1(v___x_676_, v___x_701_, v___x_703_);
v___x_705_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_676_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41));
v___x_708_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_709_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2));
v___x_710_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_709_, v_currMacroScope_673_);
v___x_711_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6));
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v___x_676_);
lean_ctor_set(v___x_712_, 1, v___x_708_);
lean_ctor_set(v___x_712_, 2, v___x_710_);
lean_ctor_set(v___x_712_, 3, v___x_711_);
lean_inc_n(v___x_704_, 2);
v___x_713_ = l_Lean_Syntax_node1(v___x_676_, v___x_683_, v___x_704_);
v___x_714_ = l_Lean_Syntax_node2(v___x_676_, v___x_707_, v___x_712_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node1(v___x_676_, v___x_683_, v___x_714_);
v___x_716_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52));
v___x_717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_676_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
lean_inc_ref_n(v___x_717_, 2);
lean_inc(v___x_700_);
v___x_718_ = l_Lean_Syntax_node5(v___x_676_, v___x_691_, v___x_700_, v___x_704_, v___x_706_, v___x_715_, v___x_717_);
v___x_719_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53));
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_676_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_Syntax_node3(v___x_676_, v___x_690_, v___x_718_, v___x_720_, v___x_704_);
v___x_722_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
v___x_723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_723_, 0, v___x_676_);
lean_ctor_set(v___x_723_, 1, v___x_683_);
lean_ctor_set(v___x_723_, 2, v___x_722_);
lean_inc_ref_n(v___x_723_, 7);
v___x_724_ = l_Lean_Syntax_node3(v___x_676_, v___x_688_, v___x_689_, v___x_721_, v___x_723_);
v___x_725_ = l_Lean_Syntax_node1(v___x_676_, v___x_683_, v___x_724_);
v___x_726_ = l_Lean_Syntax_node1(v___x_676_, v___x_682_, v___x_725_);
v___x_727_ = l_Lean_Syntax_node1(v___x_676_, v___x_681_, v___x_726_);
v___x_728_ = l_Lean_Syntax_node2(v___x_676_, v___x_684_, v___x_686_, v___x_727_);
v___x_729_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55));
v___x_730_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_676_);
lean_ctor_set(v___x_731_, 1, v___x_729_);
v___x_732_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58));
v___x_733_ = l_Lean_Syntax_node1(v___x_676_, v___x_732_, v___x_723_);
v___x_734_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59));
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_676_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61));
v___x_737_ = lean_obj_once(&l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1, &l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1_once, _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1);
v___x_738_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2));
v___x_739_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_738_, v_currMacroScope_673_);
v___x_740_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5));
v___x_741_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_741_, 0, v___x_676_);
lean_ctor_set(v___x_741_, 1, v___x_737_);
lean_ctor_set(v___x_741_, 2, v___x_739_);
lean_ctor_set(v___x_741_, 3, v___x_740_);
v___x_742_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69));
v___x_743_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71));
v___x_744_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_676_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73));
v___x_747_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74));
v___x_748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_676_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
v___x_749_ = l_Lean_Syntax_node1(v___x_676_, v___x_747_, v___x_748_);
v___x_750_ = l_Lean_Syntax_node1(v___x_676_, v___x_683_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___x_676_, v___x_682_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___x_676_, v___x_681_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node2(v___x_676_, v___x_743_, v___x_745_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node3(v___x_676_, v___x_742_, v___x_700_, v___x_753_, v___x_717_);
v___x_755_ = l_Lean_Syntax_node1(v___x_676_, v___x_683_, v___x_754_);
v___x_756_ = l_Lean_Syntax_node2(v___x_676_, v___x_707_, v___x_741_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node3(v___x_676_, v___x_736_, v___x_723_, v___x_723_, v___x_756_);
v___x_758_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_676_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_Syntax_node2(v___x_676_, v___x_683_, v___x_757_, v___x_759_);
v___x_761_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_676_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_Syntax_node3(v___x_676_, v___x_683_, v___x_735_, v___x_760_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node6(v___x_676_, v___x_730_, v___x_731_, v___x_733_, v___x_723_, v___x_723_, v___x_763_, v___x_723_);
v___x_765_ = l_Lean_Syntax_node3(v___x_676_, v___x_683_, v___x_728_, v___x_723_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___x_676_, v___x_682_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node1(v___x_676_, v___x_681_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node3(v___x_676_, v___x_678_, v___x_680_, v___x_767_, v___x_717_);
v___x_769_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77));
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_676_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78));
v___x_772_ = ((lean_object*)(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_676_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
v___x_774_ = l_Lean_Syntax_node1(v___x_676_, v___x_772_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node3(v___x_676_, v___x_677_, v___x_768_, v___x_770_, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v_a_667_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___boxed(lean_object* v_x_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4(v_x_777_, v_a_778_, v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_780_;
}
}
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
