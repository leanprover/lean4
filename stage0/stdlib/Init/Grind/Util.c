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
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___redArg(lean_object* v_a_21_){
_start:
{
lean_inc(v_a_21_);
return v_a_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___redArg___boxed(lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Grind_abstractFn___redArg(v_a_22_);
lean_dec(v_a_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn(lean_object* v_00_u03b1_24_, lean_object* v_a_25_){
_start:
{
lean_inc(v_a_25_);
return v_a_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___boxed(lean_object* v_00_u03b1_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Grind_abstractFn(v_00_u03b1_26_, v_a_27_);
lean_dec(v_a_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_nat_add(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset___boxed(lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Grind_offset(v_a_32_, v_b_33_);
lean_dec(v_b_33_);
lean_dec(v_a_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander(lean_object* v_stx_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_49_);
v___x_53_ = l_Lean_Syntax_isOfKind(v_stx_49_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_stx_49_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v_a_51_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = l_Lean_Syntax_getArg(v_stx_49_, v___x_56_);
lean_dec(v_stx_49_);
lean_inc(v___x_57_);
v___x_58_ = l_Lean_Syntax_matchesNull(v___x_57_, v___x_56_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v___x_57_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v_a_51_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = l_Lean_Syntax_getArg(v___x_57_, v___x_61_);
lean_dec(v___x_57_);
v___x_63_ = 0;
v___x_64_ = l_Lean_SourceInfo_fromRef(v_a_50_, v___x_63_);
v___x_65_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__6));
v___x_66_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__7));
lean_inc_n(v___x_64_, 2);
v___x_67_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__8));
v___x_69_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_64_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = l_Lean_Syntax_node3(v___x_64_, v___x_65_, v___x_67_, v___x_62_, v___x_69_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_a_51_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander___boxed(lean_object* v_stx_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Grind_nestedProofUnexpander(v_stx_72_, v_a_73_, v_a_74_);
lean_dec(v_a_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___redArg(lean_object* v_stx_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_76_);
v___x_79_ = l_Lean_Syntax_isOfKind(v_stx_76_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_stx_76_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_a_77_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = l_Lean_Syntax_getArg(v_stx_76_, v___x_82_);
lean_dec(v_stx_76_);
lean_inc(v___x_83_);
v___x_84_ = l_Lean_Syntax_matchesNull(v___x_83_, v___x_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v___x_83_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_a_77_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_Lean_Syntax_getArg(v___x_83_, v___x_87_);
lean_dec(v___x_83_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_a_77_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander(lean_object* v_stx_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Grind_matchCondUnexpander___redArg(v_stx_90_, v_a_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___boxed(lean_object* v_stx_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Grind_matchCondUnexpander(v_stx_94_, v_a_95_, v_a_96_);
lean_dec(v_a_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander(lean_object* v_stx_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_102_);
v___x_106_ = l_Lean_Syntax_isOfKind(v_stx_102_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_stx_102_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_a_104_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = l_Lean_Syntax_getArg(v_stx_102_, v___x_109_);
lean_dec(v_stx_102_);
v___x_111_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_110_);
v___x_112_ = l_Lean_Syntax_matchesNull(v___x_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_104_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = l_Lean_Syntax_getArg(v___x_110_, v___x_115_);
v___x_117_ = l_Lean_Syntax_getArg(v___x_110_, v___x_109_);
lean_dec(v___x_110_);
v___x_118_ = 0;
v___x_119_ = l_Lean_SourceInfo_fromRef(v_a_103_, v___x_118_);
v___x_120_ = ((lean_object*)(l_Lean_Grind_eqMatchUnexpander___closed__1));
v___x_121_ = ((lean_object*)(l_Lean_Grind_eqMatchUnexpander___closed__2));
lean_inc(v___x_119_);
v___x_122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_119_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = l_Lean_Syntax_node3(v___x_119_, v___x_120_, v___x_116_, v___x_122_, v___x_117_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v_a_104_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander___boxed(lean_object* v_stx_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Grind_eqMatchUnexpander(v_stx_125_, v_a_126_, v_a_127_);
lean_dec(v_a_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander(lean_object* v_stx_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_133_);
v___x_137_ = l_Lean_Syntax_isOfKind(v_stx_133_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_stx_133_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_135_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = l_Lean_Syntax_getArg(v_stx_133_, v___x_140_);
lean_dec(v_stx_133_);
v___x_142_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_141_);
v___x_143_ = l_Lean_Syntax_matchesNull(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_135_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_Lean_Syntax_getArg(v___x_141_, v___x_146_);
v___x_148_ = l_Lean_Syntax_getArg(v___x_141_, v___x_140_);
lean_dec(v___x_141_);
v___x_149_ = 0;
v___x_150_ = l_Lean_SourceInfo_fromRef(v_a_134_, v___x_149_);
v___x_151_ = ((lean_object*)(l_Lean_Grind_offsetUnexpander___closed__1));
v___x_152_ = ((lean_object*)(l_Lean_Grind_offsetUnexpander___closed__2));
lean_inc(v___x_150_);
v___x_153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_150_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = l_Lean_Syntax_node3(v___x_150_, v___x_151_, v___x_147_, v___x_153_, v___x_148_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_135_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander___boxed(lean_object* v_stx_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Grind_offsetUnexpander(v_stx_156_, v_a_157_, v_a_158_);
lean_dec(v_a_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander(lean_object* v_stx_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_164_);
v___x_168_ = l_Lean_Syntax_isOfKind(v_stx_164_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_stx_164_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_166_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = l_Lean_Syntax_getArg(v_stx_164_, v___x_171_);
lean_dec(v_stx_164_);
lean_inc(v___x_172_);
v___x_173_ = l_Lean_Syntax_matchesNull(v___x_172_, v___x_171_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v___x_172_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_a_166_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = l_Lean_Syntax_getArg(v___x_172_, v___x_176_);
lean_dec(v___x_172_);
v___x_178_ = 0;
v___x_179_ = l_Lean_SourceInfo_fromRef(v_a_165_, v___x_178_);
v___x_180_ = ((lean_object*)(l_Lean_Grind_natCastUnexpander___closed__1));
v___x_181_ = ((lean_object*)(l_Lean_Grind_natCastUnexpander___closed__2));
lean_inc(v___x_179_);
v___x_182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = l_Lean_Syntax_node2(v___x_179_, v___x_180_, v___x_182_, v___x_177_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_166_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander___boxed(lean_object* v_stx_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Grind_natCastUnexpander(v_stx_185_, v_a_186_, v_a_187_);
lean_dec(v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg(lean_object* v_a_189_){
_start:
{
lean_inc(v_a_189_);
return v_a_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg___boxed(lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Grind_Marker___redArg(v_a_190_);
lean_dec(v_a_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker(lean_object* v_00_u03b1_192_, lean_object* v_a_193_){
_start:
{
lean_inc(v_a_193_);
return v_a_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___boxed(lean_object* v_00_u03b1_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Grind_Marker(v_00_u03b1_194_, v_a_195_);
lean_dec(v_a_195_);
return v_res_196_;
}
}
static lean_object* _init_l_Lean_Grind_markerUnexpander___redArg___closed__14(void){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Array_mkArray0(lean_box(0));
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg(lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_235_ = 0;
v___x_236_ = l_Lean_SourceInfo_fromRef(v_a_233_, v___x_235_);
v___x_237_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__1));
v___x_238_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__2));
lean_inc_n(v___x_236_, 8);
v___x_239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_236_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__5));
v___x_241_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__7));
v___x_242_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__9));
v___x_243_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__10));
v___x_244_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__11));
v___x_245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_236_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
v___x_246_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__13));
v___x_247_ = lean_obj_once(&l_Lean_Grind_markerUnexpander___redArg___closed__14, &l_Lean_Grind_markerUnexpander___redArg___closed__14_once, _init_l_Lean_Grind_markerUnexpander___redArg___closed__14);
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_236_);
lean_ctor_set(v___x_248_, 1, v___x_242_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
lean_inc_ref_n(v___x_248_, 3);
v___x_249_ = l_Lean_Syntax_node1(v___x_236_, v___x_246_, v___x_248_);
v___x_250_ = l_Lean_Syntax_node5(v___x_236_, v___x_244_, v___x_245_, v___x_249_, v___x_248_, v___x_248_, v___x_248_);
v___x_251_ = l_Lean_Syntax_node1(v___x_236_, v___x_242_, v___x_250_);
v___x_252_ = l_Lean_Syntax_node1(v___x_236_, v___x_241_, v___x_251_);
v___x_253_ = l_Lean_Syntax_node1(v___x_236_, v___x_240_, v___x_252_);
v___x_254_ = l_Lean_Syntax_node2(v___x_236_, v___x_237_, v___x_239_, v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_234_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg___boxed(lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Grind_markerUnexpander___redArg(v_a_256_, v_a_257_);
lean_dec(v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander(lean_object* v_x_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Grind_markerUnexpander___redArg(v_a_260_, v_a_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___boxed(lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Grind_markerUnexpander(v_x_263_, v_a_264_, v_a_265_);
lean_dec(v_a_264_);
lean_dec(v_x_263_);
return v_res_266_;
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
