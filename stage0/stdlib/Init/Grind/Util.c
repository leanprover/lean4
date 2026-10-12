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
lean_object* l_Array_mkArray0___redArg();
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
uint8_t l_Lean_Grind_nestedDecidable___redArg(uint8_t v_h_1_){
_start:
{
return v_h_1_;
}
}
LEAN_EXPORT void l_Lean_Grind_nestedDecidable___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_h_1_ = stack[0].m_num;
uint8_t v_res_2_;
v_res_2_ = l_Lean_Grind_nestedDecidable___redArg(v_h_1_);
stack->m_num = v_res_2_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedDecidable___redArg___boxed(lean_object* v_h_3_){
_start:
{
uint8_t v_h_boxed_4_; uint8_t v_res_5_; lean_object* v_r_6_; 
v_h_boxed_4_ = lean_unbox(v_h_3_);
v_res_5_ = l_Lean_Grind_nestedDecidable___redArg(v_h_boxed_4_);
v_r_6_ = lean_box(v_res_5_);
return v_r_6_;
}
}
uint8_t l_Lean_Grind_nestedDecidable(lean_object* v_p_7_, uint8_t v_h_8_){
_start:
{
return v_h_8_;
}
}
LEAN_EXPORT void l_Lean_Grind_nestedDecidable_0interp(lean_interpreter_value* stack)
{
uint8_t v_h_8_ = stack[1].m_num;
uint8_t v_res_9_;
v_res_9_ = l_Lean_Grind_nestedDecidable(lean_box(0), v_h_8_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedDecidable___boxed(lean_object* v_p_10_, lean_object* v_h_11_){
_start:
{
uint8_t v_h_boxed_12_; uint8_t v_res_13_; lean_object* v_r_14_; 
v_h_boxed_12_ = lean_unbox(v_h_11_);
v_res_13_ = l_Lean_Grind_nestedDecidable(v_p_10_, v_h_boxed_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___redArg(lean_object* v_a_15_){
_start:
{
lean_inc(v_a_15_);
return v_a_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___redArg___boxed(lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Grind_simpMatchDiscrsOnly___redArg(v_a_16_);
lean_dec(v_a_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly(lean_object* v_00_u03b1_18_, lean_object* v_a_19_){
_start:
{
lean_inc(v_a_19_);
return v_a_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_simpMatchDiscrsOnly___boxed(lean_object* v_00_u03b1_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Grind_simpMatchDiscrsOnly(v_00_u03b1_20_, v_a_21_);
lean_dec(v_a_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___redArg(lean_object* v_a_23_){
_start:
{
lean_inc(v_a_23_);
return v_a_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___redArg___boxed(lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Grind_abstractFn___redArg(v_a_24_);
lean_dec(v_a_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn(lean_object* v_00_u03b1_26_, lean_object* v_a_27_){
_start:
{
lean_inc(v_a_27_);
return v_a_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_abstractFn___boxed(lean_object* v_00_u03b1_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Grind_abstractFn(v_00_u03b1_28_, v_a_29_);
lean_dec(v_a_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset(lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_nat_add(v_a_31_, v_b_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offset___boxed(lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Grind_offset(v_a_34_, v_b_35_);
lean_dec(v_b_35_);
lean_dec(v_a_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander(lean_object* v_stx_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_51_);
v___x_55_ = l_Lean_Syntax_isOfKind(v_stx_51_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_stx_51_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v_a_53_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = l_Lean_Syntax_getArg(v_stx_51_, v___x_58_);
lean_dec(v_stx_51_);
lean_inc(v___x_59_);
v___x_60_ = l_Lean_Syntax_matchesNull(v___x_59_, v___x_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v___x_59_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_a_53_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = l_Lean_Syntax_getArg(v___x_59_, v___x_63_);
lean_dec(v___x_59_);
v___x_65_ = 0;
v___x_66_ = l_Lean_SourceInfo_fromRef(v_a_52_, v___x_65_);
v___x_67_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__6));
v___x_68_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__7));
lean_inc_n(v___x_66_, 2);
v___x_69_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_66_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__8));
v___x_71_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_66_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_Syntax_node3(v___x_66_, v___x_67_, v___x_69_, v___x_64_, v___x_71_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_a_53_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nestedProofUnexpander___boxed(lean_object* v_stx_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Grind_nestedProofUnexpander(v_stx_74_, v_a_75_, v_a_76_);
lean_dec(v_a_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___redArg(lean_object* v_stx_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_78_);
v___x_81_ = l_Lean_Syntax_isOfKind(v_stx_78_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_stx_78_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_a_79_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = l_Lean_Syntax_getArg(v_stx_78_, v___x_84_);
lean_dec(v_stx_78_);
lean_inc(v___x_85_);
v___x_86_ = l_Lean_Syntax_matchesNull(v___x_85_, v___x_84_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v___x_85_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_a_79_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Lean_Syntax_getArg(v___x_85_, v___x_89_);
lean_dec(v___x_85_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v_a_79_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander(lean_object* v_stx_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Grind_matchCondUnexpander___redArg(v_stx_92_, v_a_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_matchCondUnexpander___boxed(lean_object* v_stx_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Grind_matchCondUnexpander(v_stx_96_, v_a_97_, v_a_98_);
lean_dec(v_a_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander(lean_object* v_stx_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_104_);
v___x_108_ = l_Lean_Syntax_isOfKind(v_stx_104_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_stx_104_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v_a_106_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = l_Lean_Syntax_getArg(v_stx_104_, v___x_111_);
lean_dec(v_stx_104_);
v___x_113_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_112_);
v___x_114_ = l_Lean_Syntax_matchesNull(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_a_106_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = l_Lean_Syntax_getArg(v___x_112_, v___x_117_);
v___x_119_ = l_Lean_Syntax_getArg(v___x_112_, v___x_111_);
lean_dec(v___x_112_);
v___x_120_ = 0;
v___x_121_ = l_Lean_SourceInfo_fromRef(v_a_105_, v___x_120_);
v___x_122_ = ((lean_object*)(l_Lean_Grind_eqMatchUnexpander___closed__1));
v___x_123_ = ((lean_object*)(l_Lean_Grind_eqMatchUnexpander___closed__2));
lean_inc(v___x_121_);
v___x_124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_121_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = l_Lean_Syntax_node3(v___x_121_, v___x_122_, v___x_118_, v___x_124_, v___x_119_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v_a_106_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_eqMatchUnexpander___boxed(lean_object* v_stx_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Grind_eqMatchUnexpander(v_stx_127_, v_a_128_, v_a_129_);
lean_dec(v_a_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander(lean_object* v_stx_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_135_);
v___x_139_ = l_Lean_Syntax_isOfKind(v_stx_135_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_stx_135_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_a_137_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = l_Lean_Syntax_getArg(v_stx_135_, v___x_142_);
lean_dec(v_stx_135_);
v___x_144_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_143_);
v___x_145_ = l_Lean_Syntax_matchesNull(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_a_137_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_Lean_Syntax_getArg(v___x_143_, v___x_148_);
v___x_150_ = l_Lean_Syntax_getArg(v___x_143_, v___x_142_);
lean_dec(v___x_143_);
v___x_151_ = 0;
v___x_152_ = l_Lean_SourceInfo_fromRef(v_a_136_, v___x_151_);
v___x_153_ = ((lean_object*)(l_Lean_Grind_offsetUnexpander___closed__1));
v___x_154_ = ((lean_object*)(l_Lean_Grind_offsetUnexpander___closed__2));
lean_inc(v___x_152_);
v___x_155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_152_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = l_Lean_Syntax_node3(v___x_152_, v___x_153_, v___x_149_, v___x_155_, v___x_150_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_137_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_offsetUnexpander___boxed(lean_object* v_stx_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Grind_offsetUnexpander(v_stx_158_, v_a_159_, v_a_160_);
lean_dec(v_a_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander(lean_object* v_stx_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Grind_nestedProofUnexpander___closed__4));
lean_inc(v_stx_166_);
v___x_170_ = l_Lean_Syntax_isOfKind(v_stx_166_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_stx_166_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_a_168_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = l_Lean_Syntax_getArg(v_stx_166_, v___x_173_);
lean_dec(v_stx_166_);
lean_inc(v___x_174_);
v___x_175_ = l_Lean_Syntax_matchesNull(v___x_174_, v___x_173_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v___x_174_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_a_168_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Lean_Syntax_getArg(v___x_174_, v___x_178_);
lean_dec(v___x_174_);
v___x_180_ = 0;
v___x_181_ = l_Lean_SourceInfo_fromRef(v_a_167_, v___x_180_);
v___x_182_ = ((lean_object*)(l_Lean_Grind_natCastUnexpander___closed__1));
v___x_183_ = ((lean_object*)(l_Lean_Grind_natCastUnexpander___closed__2));
lean_inc(v___x_181_);
v___x_184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = l_Lean_Syntax_node2(v___x_181_, v___x_182_, v___x_184_, v___x_179_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_168_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_natCastUnexpander___boxed(lean_object* v_stx_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Grind_natCastUnexpander(v_stx_187_, v_a_188_, v_a_189_);
lean_dec(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg(lean_object* v_a_191_){
_start:
{
lean_inc(v_a_191_);
return v_a_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___redArg___boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Grind_Marker___redArg(v_a_192_);
lean_dec(v_a_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker(lean_object* v_00_u03b1_194_, lean_object* v_a_195_){
_start:
{
lean_inc(v_a_195_);
return v_a_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Marker___boxed(lean_object* v_00_u03b1_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Grind_Marker(v_00_u03b1_196_, v_a_197_);
lean_dec(v_a_197_);
return v_res_198_;
}
}
static lean_object* _init_l_Lean_Grind_markerUnexpander___redArg___closed__14(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Array_mkArray0___redArg();
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg(lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_237_ = 0;
v___x_238_ = l_Lean_SourceInfo_fromRef(v_a_235_, v___x_237_);
v___x_239_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__1));
v___x_240_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__2));
lean_inc_n(v___x_238_, 8);
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__5));
v___x_243_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__7));
v___x_244_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__9));
v___x_245_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__10));
v___x_246_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__11));
v___x_247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_238_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
v___x_248_ = ((lean_object*)(l_Lean_Grind_markerUnexpander___redArg___closed__13));
v___x_249_ = lean_obj_once(&l_Lean_Grind_markerUnexpander___redArg___closed__14, &l_Lean_Grind_markerUnexpander___redArg___closed__14_once, _init_l_Lean_Grind_markerUnexpander___redArg___closed__14);
v___x_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_250_, 0, v___x_238_);
lean_ctor_set(v___x_250_, 1, v___x_244_);
lean_ctor_set(v___x_250_, 2, v___x_249_);
lean_inc_ref_n(v___x_250_, 3);
v___x_251_ = l_Lean_Syntax_node1(v___x_238_, v___x_248_, v___x_250_);
v___x_252_ = l_Lean_Syntax_node5(v___x_238_, v___x_246_, v___x_247_, v___x_251_, v___x_250_, v___x_250_, v___x_250_);
v___x_253_ = l_Lean_Syntax_node1(v___x_238_, v___x_244_, v___x_252_);
v___x_254_ = l_Lean_Syntax_node1(v___x_238_, v___x_243_, v___x_253_);
v___x_255_ = l_Lean_Syntax_node1(v___x_238_, v___x_242_, v___x_254_);
v___x_256_ = l_Lean_Syntax_node2(v___x_238_, v___x_239_, v___x_241_, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_a_236_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___redArg___boxed(lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Grind_markerUnexpander___redArg(v_a_258_, v_a_259_);
lean_dec(v_a_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander(lean_object* v_x_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Grind_markerUnexpander___redArg(v_a_262_, v_a_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_markerUnexpander___boxed(lean_object* v_x_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Grind_markerUnexpander(v_x_265_, v_a_266_, v_a_267_);
lean_dec(v_a_266_);
lean_dec(v_x_265_);
return v_res_268_;
}
}
lean_object* runtime_initialize_Init_Data_Cast(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
