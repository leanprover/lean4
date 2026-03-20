// Lean compiler output
// Module: Init.Grind.Util
// Imports: public import Init.Data.Cast public import Init.Grind.Tactics public meta import Init.Grind.Tactics import Init.Classical
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_nestedDecidable___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_nestedDecidable___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_nestedDecidable(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_nestedDecidable___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_offset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_offset___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_nestedProofUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__0 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__0_value;
static const lean_string_object l_Lean_Grind_nestedProofUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__1 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__1_value;
static const lean_string_object l_Lean_Grind_nestedProofUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__2 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__2_value;
static const lean_string_object l_Lean_Grind_nestedProofUnexpander___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__3 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__3_value;
static const lean_ctor_object l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_0),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_1),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Grind_nestedProofUnexpander___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_2),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__4 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__4_value;
static const lean_string_object l_Lean_Grind_nestedProofUnexpander___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term‹_›"};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__5 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__5_value;
static const lean_ctor_object l_Lean_Grind_nestedProofUnexpander___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__5_value),LEAN_SCALAR_PTR_LITERAL(149, 139, 117, 210, 91, 226, 103, 115)}};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__6 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__6_value;
static const lean_string_object l_Lean_Grind_nestedProofUnexpander___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "‹"};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__7 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__7_value;
static const lean_string_object l_Lean_Grind_nestedProofUnexpander___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "›"};
static const lean_object* l_Lean_Grind_nestedProofUnexpander___closed__8 = (const lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_eqMatchUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l_Lean_Grind_eqMatchUnexpander___closed__0 = (const lean_object*)&l_Lean_Grind_eqMatchUnexpander___closed__0_value;
static const lean_ctor_object l_Lean_Grind_eqMatchUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_eqMatchUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l_Lean_Grind_eqMatchUnexpander___closed__1 = (const lean_object*)&l_Lean_Grind_eqMatchUnexpander___closed__1_value;
static const lean_string_object l_Lean_Grind_eqMatchUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Lean_Grind_eqMatchUnexpander___closed__2 = (const lean_object*)&l_Lean_Grind_eqMatchUnexpander___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_offsetUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_+_"};
static const lean_object* l_Lean_Grind_offsetUnexpander___closed__0 = (const lean_object*)&l_Lean_Grind_offsetUnexpander___closed__0_value;
static const lean_ctor_object l_Lean_Grind_offsetUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_offsetUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 160, 89, 154, 247, 230, 95, 119)}};
static const lean_object* l_Lean_Grind_offsetUnexpander___closed__1 = (const lean_object*)&l_Lean_Grind_offsetUnexpander___closed__1_value;
static const lean_string_object l_Lean_Grind_offsetUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Grind_offsetUnexpander___closed__2 = (const lean_object*)&l_Lean_Grind_offsetUnexpander___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_natCastUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coeNotation"};
static const lean_object* l_Lean_Grind_natCastUnexpander___closed__0 = (const lean_object*)&l_Lean_Grind_natCastUnexpander___closed__0_value;
static const lean_ctor_object l_Lean_Grind_natCastUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_natCastUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 100, 71, 170, 251, 12, 50, 58)}};
static const lean_object* l_Lean_Grind_natCastUnexpander___closed__1 = (const lean_object*)&l_Lean_Grind_natCastUnexpander___closed__1_value;
static const lean_string_object l_Lean_Grind_natCastUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↑"};
static const lean_object* l_Lean_Grind_natCastUnexpander___closed__2 = (const lean_object*)&l_Lean_Grind_natCastUnexpander___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Marker(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__0 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__1 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__1_value;
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__2 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__2_value;
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__3 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__3_value;
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__4 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__5 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__5_value;
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__6 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_2),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__7 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__7_value;
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__8 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__9 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__9_value;
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__10 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_1),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_2),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__11 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__11_value;
static const lean_string_object l_Lean_Grind_markerUnexpander___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__12 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Grind_nestedProofUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_markerUnexpander___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_2),((lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__13 = (const lean_object*)&l_Lean_Grind_markerUnexpander___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Grind_markerUnexpander___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_markerUnexpander___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_nestedDecidable___redArg(uint8_t v_h_1_){
_start:
{
return v_h_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedDecidable___redArg___boxed(lean_object* v_h_2_){
_start:
{
uint8_t v_h_boxed_3_; uint8_t v_res_4_; lean_object* v_r_5_; 
v_h_boxed_3_ = lean_unbox(v_h_2_);
v_res_4_ = l_Lean_Grind_nestedDecidable___redArg(v_h_boxed_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_nestedDecidable(lean_object* v_p_6_, uint8_t v_h_7_){
_start:
{
return v_h_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedDecidable___boxed(lean_object* v_p_8_, lean_object* v_h_9_){
_start:
{
uint8_t v_h_boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_h_boxed_10_ = lean_unbox(v_h_9_);
v_res_11_ = l_Lean_Grind_nestedDecidable(v_p_8_, v_h_boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___redArg(lean_object* v_a_13_){
_start:
{
lean_inc(v_a_13_);
return v_a_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___redArg___boxed(lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Grind_simpMatchDiscrsOnly___redArg(v_a_14_);
lean_dec(v_a_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly(lean_object* v_00_u03b1_16_, lean_object* v_a_17_){
_start:
{
lean_inc(v_a_17_);
return v_a_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___boxed(lean_object* v_00_u03b1_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Grind_simpMatchDiscrsOnly(v_00_u03b1_18_, v_a_19_);
lean_dec(v_a_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset(lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_nat_add(v_a_21_, v_b_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset___boxed(lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Grind_offset(v_a_24_, v_b_25_);
lean_dec(v_b_25_);
lean_dec(v_a_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander(lean_object* v_stx_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_41_);
v___x_45_ = l_Lean_Syntax_isOfKind(v_stx_41_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_stx_41_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v_a_43_);
return v___x_47_;
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_48_ = lean_unsigned_to_nat(1u);
v___x_49_ = l_Lean_Syntax_getArg(v_stx_41_, v___x_48_);
lean_dec(v_stx_41_);
lean_inc(v___x_49_);
v___x_50_ = l_Lean_Syntax_matchesNull(v___x_49_, v___x_48_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v___x_49_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v_a_43_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l_Lean_Syntax_getArg(v___x_49_, v___x_53_);
lean_dec(v___x_49_);
v___x_55_ = 0;
v___x_56_ = l_Lean_SourceInfo_fromRef(v_a_42_, v___x_55_);
v___x_57_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__6));
v___x_58_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__7));
lean_inc(v___x_56_);
v___x_59_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_56_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__8));
lean_inc(v___x_56_);
v___x_61_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_56_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = l_Lean_Syntax_node3(v___x_56_, v___x_57_, v___x_59_, v___x_54_, v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v_a_43_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander___boxed(lean_object* v_stx_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Grind_nestedProofUnexpander(v_stx_64_, v_a_65_, v_a_66_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___redArg(lean_object* v_stx_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_68_);
v___x_71_ = l_Lean_Syntax_isOfKind(v_stx_68_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_stx_68_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_a_69_);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = l_Lean_Syntax_getArg(v_stx_68_, v___x_74_);
lean_dec(v_stx_68_);
lean_inc(v___x_75_);
v___x_76_ = l_Lean_Syntax_matchesNull(v___x_75_, v___x_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v___x_75_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v_a_69_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = l_Lean_Syntax_getArg(v___x_75_, v___x_79_);
lean_dec(v___x_75_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_a_69_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander(lean_object* v_stx_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Grind_matchCondUnexpander___redArg(v_stx_82_, v_a_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___boxed(lean_object* v_stx_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Grind_matchCondUnexpander(v_stx_86_, v_a_87_, v_a_88_);
lean_dec(v_a_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander(lean_object* v_stx_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_94_);
v___x_98_ = l_Lean_Syntax_isOfKind(v_stx_94_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_stx_94_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_a_96_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = l_Lean_Syntax_getArg(v_stx_94_, v___x_101_);
lean_dec(v_stx_94_);
v___x_103_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_102_);
v___x_104_ = l_Lean_Syntax_matchesNull(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_a_96_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = l_Lean_Syntax_getArg(v___x_102_, v___x_107_);
v___x_109_ = l_Lean_Syntax_getArg(v___x_102_, v___x_101_);
lean_dec(v___x_102_);
v___x_110_ = 0;
v___x_111_ = l_Lean_SourceInfo_fromRef(v_a_95_, v___x_110_);
v___x_112_ = ((lean_object*)(l_Lean_Grind_eqMatchUnexpander___closed__1));
v___x_113_ = ((lean_object*)(l_Lean_Grind_eqMatchUnexpander___closed__2));
lean_inc(v___x_111_);
v___x_114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_111_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = l_Lean_Syntax_node3(v___x_111_, v___x_112_, v___x_108_, v___x_114_, v___x_109_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_a_96_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander___boxed(lean_object* v_stx_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Grind_eqMatchUnexpander(v_stx_117_, v_a_118_, v_a_119_);
lean_dec(v_a_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander(lean_object* v_stx_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_125_);
v___x_129_ = l_Lean_Syntax_isOfKind(v_stx_125_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_stx_125_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_127_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = l_Lean_Syntax_getArg(v_stx_125_, v___x_132_);
lean_dec(v_stx_125_);
v___x_134_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_133_);
v___x_135_ = l_Lean_Syntax_matchesNull(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_a_127_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = l_Lean_Syntax_getArg(v___x_133_, v___x_138_);
v___x_140_ = l_Lean_Syntax_getArg(v___x_133_, v___x_132_);
lean_dec(v___x_133_);
v___x_141_ = 0;
v___x_142_ = l_Lean_SourceInfo_fromRef(v_a_126_, v___x_141_);
v___x_143_ = ((lean_object*)(l_Lean_Grind_offsetUnexpander___closed__1));
v___x_144_ = ((lean_object*)(l_Lean_Grind_offsetUnexpander___closed__2));
lean_inc(v___x_142_);
v___x_145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_142_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = l_Lean_Syntax_node3(v___x_142_, v___x_143_, v___x_139_, v___x_145_, v___x_140_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_a_127_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander___boxed(lean_object* v_stx_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Grind_offsetUnexpander(v_stx_148_, v_a_149_, v_a_150_);
lean_dec(v_a_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander(lean_object* v_stx_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_156_);
v___x_160_ = l_Lean_Syntax_isOfKind(v_stx_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_stx_156_);
v___x_161_ = lean_box(0);
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = l_Lean_Syntax_getArg(v_stx_156_, v___x_163_);
lean_dec(v_stx_156_);
lean_inc(v___x_164_);
v___x_165_ = l_Lean_Syntax_matchesNull(v___x_164_, v___x_163_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v___x_164_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_158_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_Lean_Syntax_getArg(v___x_164_, v___x_168_);
lean_dec(v___x_164_);
v___x_170_ = 0;
v___x_171_ = l_Lean_SourceInfo_fromRef(v_a_157_, v___x_170_);
v___x_172_ = ((lean_object*)(l_Lean_Grind_natCastUnexpander___closed__1));
v___x_173_ = ((lean_object*)(l_Lean_Grind_natCastUnexpander___closed__2));
lean_inc(v___x_171_);
v___x_174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_171_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_Syntax_node2(v___x_171_, v___x_172_, v___x_174_, v___x_169_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_158_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander___boxed(lean_object* v_stx_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Grind_natCastUnexpander(v_stx_177_, v_a_178_, v_a_179_);
lean_dec(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg(lean_object* v_a_181_){
_start:
{
lean_inc(v_a_181_);
return v_a_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg___boxed(lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Grind_Marker___redArg(v_a_182_);
lean_dec(v_a_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker(lean_object* v_00_u03b1_184_, lean_object* v_a_185_){
_start:
{
lean_inc(v_a_185_);
return v_a_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___boxed(lean_object* v_00_u03b1_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Grind_Marker(v_00_u03b1_186_, v_a_187_);
lean_dec(v_a_187_);
return v_res_188_;
}
}
static lean_object* _init_l_Lean_Grind_markerUnexpander___redArg___closed__14(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Array_mkArray0(lean_box(0));
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg(lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_227_ = 0;
v___x_228_ = l_Lean_SourceInfo_fromRef(v_a_225_, v___x_227_);
v___x_229_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__1));
v___x_230_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__2));
lean_inc(v___x_228_);
v___x_231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_228_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__5));
v___x_233_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__7));
v___x_234_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__9));
v___x_235_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__10));
v___x_236_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__11));
lean_inc(v___x_228_);
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_228_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
v___x_238_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__13));
v___x_239_ = lean_obj_once(&l_Lean_Grind_markerUnexpander___redArg___closed__14, &l_Lean_Grind_markerUnexpander___redArg___closed__14_once, _init_l_Lean_Grind_markerUnexpander___redArg___closed__14);
lean_inc(v___x_228_);
v___x_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_240_, 0, v___x_228_);
lean_ctor_set(v___x_240_, 1, v___x_234_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
lean_inc_ref(v___x_240_);
lean_inc(v___x_228_);
v___x_241_ = l_Lean_Syntax_node1(v___x_228_, v___x_238_, v___x_240_);
lean_inc_ref_n(v___x_240_, 2);
lean_inc(v___x_228_);
v___x_242_ = l_Lean_Syntax_node5(v___x_228_, v___x_236_, v___x_237_, v___x_241_, v___x_240_, v___x_240_, v___x_240_);
lean_inc(v___x_228_);
v___x_243_ = l_Lean_Syntax_node1(v___x_228_, v___x_234_, v___x_242_);
lean_inc(v___x_228_);
v___x_244_ = l_Lean_Syntax_node1(v___x_228_, v___x_233_, v___x_243_);
lean_inc(v___x_228_);
v___x_245_ = l_Lean_Syntax_node1(v___x_228_, v___x_232_, v___x_244_);
v___x_246_ = l_Lean_Syntax_node2(v___x_228_, v___x_229_, v___x_231_, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_226_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg___boxed(lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Grind_markerUnexpander___redArg(v_a_248_, v_a_249_);
lean_dec(v_a_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander(lean_object* v_x_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Grind_markerUnexpander___redArg(v_a_252_, v_a_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___boxed(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Grind_markerUnexpander(v_x_255_, v_a_256_, v_a_257_);
lean_dec(v_a_256_);
lean_dec(v_x_255_);
return v_res_258_;
}
}
lean_object* runtime_initialize_Init_Data_Cast(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Cast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Cast(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Cast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Util(builtin);
}
#ifdef __cplusplus
}
#endif
