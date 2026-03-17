// Lean compiler output
// Module: Init.Ext
// Imports: public import Init.RCases
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extIff"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__0_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__2_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 87, 43, 146, 87, 18, 162, 246)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__4_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__6_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__7_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__9 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__9_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__10 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__10_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "iff"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__11 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__11_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__12 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__10_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__12_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__13 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__13_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__14 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__14_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__15 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__13_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__15_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__16 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__16_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__17 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__17_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__18 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__16_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__18_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__19 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__19_value;
static const lean_string_object l_Lean_Parser_Attr_extIff___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__20 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__20_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__21 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__19_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__21_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__22 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__22_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__23 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Attr_extIff___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__4_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__23_value)}};
static const lean_object* l_Lean_Parser_Attr_extIff___closed__24 = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__24_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Attr_extIff = (const lean_object*)&l_Lean_Parser_Attr_extIff___closed__24_value;
static const lean_string_object l_Lean_Parser_Attr_extFlat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extFlat"};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 244, 20, 128, 134, 196, 58, 22)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_extFlat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "flat"};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__10_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__3_value)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__4_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__15_value)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__5_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__18_value)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__21_value)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__7_value)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Attr_extFlat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__8_value)}};
static const lean_object* l_Lean_Parser_Attr_extFlat___closed__9 = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Attr_extFlat = (const lean_object*)&l_Lean_Parser_Attr_extFlat___closed__9_value;
static const lean_string_object l_Lean_Parser_Attr_ext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Parser_Attr_ext___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 19, 191, 105, 197, 110, 148, 94)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__2_value;
static const lean_string_object l_Lean_Parser_Attr_ext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Attr_ext___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_ext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__4_value;
static const lean_string_object l_Lean_Parser_Attr_ext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Attr_ext___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_ext___closed__5_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__6_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__7_value),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__24_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__4_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__8_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__9 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__9_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__10 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__7_value),((lean_object*)&l_Lean_Parser_Attr_extFlat___closed__9_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__11 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__4_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__11_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__12 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__10_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__12_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__13 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__13_value;
static const lean_string_object l_Lean_Parser_Attr_ext___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l_Lean_Parser_Attr_ext___closed__14 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_ext___closed__14_value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__15 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__16 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__7_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__16_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__17 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__4_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__17_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__18 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__13_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__18_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__19 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Attr_ext___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_ext___closed__19_value)}};
static const lean_object* l_Lean_Parser_Attr_ext___closed__20 = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__20_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Attr_ext = (const lean_object*)&l_Lean_Parser_Attr_ext___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ext"};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 70, 231, 255, 233, 213, 189, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_3),((lean_object*)&l_Lean_Parser_Attr_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 8, 190, 90, 148, 21, 56, 73)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rintroPat"};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(105, 195, 203, 253, 3, 13, 142, 19)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__12_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__13_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Parser_Attr_ext___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__14_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__16_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_ext___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__18_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__19_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__17_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__20_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_ext___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__21_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__15_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__22_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_ext___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__23_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_ext___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__24_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Ext_ext = (const lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "applyExtTheorem"};
static const lean_object* l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 70, 231, 255, 233, 213, 189, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 175, 135, 155, 23, 89, 195, 106)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "apply_ext_theorem"};
static const lean_object* l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Ext_applyExtTheorem = (const lean_object*)&l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticExt1___"};
static const lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 70, 231, 255, 233, 213, 189, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 111, 128, 11, 149, 239, 35, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ext1"};
static const lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extIff___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__14_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1______ = (const lean_object*)&l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rintro"};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 254, 242, 235, 94, 162, 254, 146)}};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_extIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Ext_ext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(26, 175, 18, 116, 252, 50, 128, 45)}};
static const lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7(void){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Array_mkArray0(lean_box(0));
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(lean_object* v_x_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1));
lean_inc(v_x_273_);
v___x_277_ = l_Lean_Syntax_isOfKind(v_x_273_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_x_273_);
v___x_278_ = lean_box(1);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_a_275_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_xs_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = l_Lean_Syntax_getArg(v_x_273_, v___x_280_);
lean_dec(v_x_273_);
v_xs_282_ = l_Lean_Syntax_getArgs(v___x_281_);
lean_dec(v___x_281_);
v___x_283_ = lean_array_get_size(v_xs_282_);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v_ref_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_ref_286_ = lean_ctor_get(v_a_274_, 5);
v___x_287_ = l_Lean_SourceInfo_fromRef(v_ref_286_, v___x_285_);
v___x_288_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1));
v___x_289_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1));
v___x_290_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2));
lean_inc(v___x_287_);
v___x_291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_287_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
lean_inc(v___x_287_);
v___x_292_ = l_Lean_Syntax_node1(v___x_287_, v___x_289_, v___x_291_);
v___x_293_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2));
lean_inc(v___x_287_);
v___x_294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_287_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3));
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4));
lean_inc(v___x_287_);
v___x_297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_287_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
v___x_298_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6));
v___x_299_ = lean_obj_once(&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7, &l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7_once, _init_l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7);
v___x_300_ = l_Array_append___redArg(v___x_299_, v_xs_282_);
lean_dec_ref(v_xs_282_);
lean_inc(v___x_287_);
v___x_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_301_, 0, v___x_287_);
lean_ctor_set(v___x_301_, 1, v___x_298_);
lean_ctor_set(v___x_301_, 2, v___x_300_);
lean_inc(v___x_287_);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_287_);
lean_ctor_set(v___x_302_, 1, v___x_298_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
lean_inc(v___x_287_);
v___x_303_ = l_Lean_Syntax_node3(v___x_287_, v___x_296_, v___x_297_, v___x_301_, v___x_302_);
v___x_304_ = l_Lean_Syntax_node3(v___x_287_, v___x_288_, v___x_292_, v___x_294_, v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_a_275_);
return v___x_305_;
}
else
{
lean_object* v_ref_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v_xs_282_);
v_ref_306_ = lean_ctor_get(v_a_274_, 5);
v___x_307_ = 0;
v___x_308_ = l_Lean_SourceInfo_fromRef(v_ref_306_, v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1));
v___x_310_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1));
v___x_311_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2));
lean_inc(v___x_308_);
v___x_312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_308_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
lean_inc(v___x_308_);
v___x_313_ = l_Lean_Syntax_node1(v___x_308_, v___x_310_, v___x_312_);
v___x_314_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2));
lean_inc(v___x_308_);
v___x_315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_308_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8));
v___x_317_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9));
lean_inc(v___x_308_);
v___x_318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_308_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
v___x_319_ = ((lean_object*)(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6));
v___x_320_ = lean_obj_once(&l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7, &l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7_once, _init_l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7);
lean_inc(v___x_308_);
v___x_321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_321_, 0, v___x_308_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
lean_inc(v___x_308_);
v___x_322_ = l_Lean_Syntax_node2(v___x_308_, v___x_317_, v___x_318_, v___x_321_);
v___x_323_ = l_Lean_Syntax_node3(v___x_308_, v___x_309_, v___x_313_, v___x_315_, v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_a_275_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___boxed(lean_object* v_x_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(v_x_325_, v_a_326_, v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_328_;
}
}
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Ext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Ext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Ext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Ext(builtin);
}
#ifdef __cplusplus
}
#endif
