// Lean compiler output
// Module: Init.Internal.Order.Basic
// Imports: public import Init.System.IO import all Init.Control.Except import all Init.Control.StateRef import all Init.Control.Option import all Init.System.ST import Init.ByCases
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
static const lean_string_object l_Lean_Order_term___u2291___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__0 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__1 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__1_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊑_"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__2 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term___u2291___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__3_value_aux_1),((lean_object*)&l_Lean_Order_term___u2291___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(63, 167, 88, 175, 201, 86, 126, 172)}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__3 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__3_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__4 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__4_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__5 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__5_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊑ "};
static const lean_object* l_Lean_Order_term___u2291___00__closed__6 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__6_value;
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__6_value)}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__7 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__7_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__8 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__8_value;
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__9 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__9_value;
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__10 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__10_value;
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__5_value),((lean_object*)&l_Lean_Order_term___u2291___00__closed__7_value),((lean_object*)&l_Lean_Order_term___u2291___00__closed__10_value)}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__11 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__11_value;
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__11_value)}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__12 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term___u2291__ = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__12_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_2),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "PartialOrder.rel"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 196, 146, 225, 179, 207, 152, 76)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value_aux_0),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 185, 40, 236, 247, 213, 206, 173)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_0),((lean_object*)&l_Lean_Order_term___u2291___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_1),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_2),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1_value;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term_u22a5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term⊥"};
static const lean_object* l_Lean_Order_term_u22a5___closed__0 = (const lean_object*)&l_Lean_Order_term_u22a5___closed__0_value;
static const lean_ctor_object l_Lean_Order_term_u22a5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term_u22a5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a5___closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term___u2291___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term_u22a5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a5___closed__1_value_aux_1),((lean_object*)&l_Lean_Order_term_u22a5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 78, 68, 112, 65, 121, 100, 195)}};
static const lean_object* l_Lean_Order_term_u22a5___closed__1 = (const lean_object*)&l_Lean_Order_term_u22a5___closed__1_value;
static const lean_string_object l_Lean_Order_term_u22a5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Lean_Order_term_u22a5___closed__2 = (const lean_object*)&l_Lean_Order_term_u22a5___closed__2_value;
static const lean_ctor_object l_Lean_Order_term_u22a5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a5___closed__2_value)}};
static const lean_object* l_Lean_Order_term_u22a5___closed__3 = (const lean_object*)&l_Lean_Order_term_u22a5___closed__3_value;
static const lean_ctor_object l_Lean_Order_term_u22a5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a5___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a5___closed__3_value)}};
static const lean_object* l_Lean_Order_term_u22a5___closed__4 = (const lean_object*)&l_Lean_Order_term_u22a5___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term_u22a5 = (const lean_object*)&l_Lean_Order_term_u22a5___closed__4_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value;
static lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 6, 155, 235, 112, 9, 162, 249)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term___u2291___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_ImplicationOrder_instOrder;
LEAN_EXPORT lean_object* l_Lean_Order_ImplicationOrder_instCompleteLattice;
LEAN_EXPORT lean_object* l_Lean_Order_ReverseImplicationOrder_instOrder;
LEAN_EXPORT lean_object* l_Lean_Order_ReverseImplicationOrder_instCompleteLattice;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_Example_findF(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Order_term___u2291___00__closed__3));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3));
x_18 = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5;
x_19 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11));
lean_inc(x_16);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13));
lean_inc(x_16);
x_24 = l_Lean_Syntax_node2(x_16, x_23, x_12, x_14);
x_25 = l_Lean_Syntax_node2(x_16, x_17, x_22, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1));
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = ((lean_object*)(l_Lean_Order_term___u2291___00__closed__3));
x_26 = ((lean_object*)(l_Lean_Order_term___u2291___00__closed__6));
lean_inc(x_24);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Syntax_node3(x_24, x_25, x_20, x_27, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Order_term_u22a5___closed__1));
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_13 = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1;
x_14 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2));
x_15 = l_Lean_addMacroScope(x_8, x_14, x_9);
x_16 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5));
x_17 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_replaceRef(x_1, x_2);
lean_dec(x_1);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = ((lean_object*)(l_Lean_Order_term_u22a5___closed__1));
x_12 = ((lean_object*)(l_Lean_Order_term_u22a5___closed__2));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Syntax_node1(x_10, x_11, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Order_instOrderPi(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Order_instCCPOPi(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Order_instCompleteLatticePi(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Order_FlatOrder_instOrder(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Order_FlatOrder_instCCPO(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_apply_1(x_1, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_apply_1(x_1, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_apply_1(x_1, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_apply_1(x_1, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Order_instPartialOrderStateT(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Order_instCCPOStateT(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Order_ImplicationOrder_instOrder() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Order_ImplicationOrder_instCompleteLattice() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Order_ReverseImplicationOrder_instOrder() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Order_ReverseImplicationOrder_instCompleteLattice() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_Example_findF(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Control_Except(uint8_t builtin);
lean_object* initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_System_ST(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5 = _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5();
lean_mark_persistent(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5);
l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1 = _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1();
lean_mark_persistent(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1);
l_Lean_Order_ImplicationOrder_instOrder = _init_l_Lean_Order_ImplicationOrder_instOrder();
lean_mark_persistent(l_Lean_Order_ImplicationOrder_instOrder);
l_Lean_Order_ImplicationOrder_instCompleteLattice = _init_l_Lean_Order_ImplicationOrder_instCompleteLattice();
lean_mark_persistent(l_Lean_Order_ImplicationOrder_instCompleteLattice);
l_Lean_Order_ReverseImplicationOrder_instOrder = _init_l_Lean_Order_ReverseImplicationOrder_instOrder();
lean_mark_persistent(l_Lean_Order_ReverseImplicationOrder_instOrder);
l_Lean_Order_ReverseImplicationOrder_instCompleteLattice = _init_l_Lean_Order_ReverseImplicationOrder_instCompleteLattice();
lean_mark_persistent(l_Lean_Order_ReverseImplicationOrder_instCompleteLattice);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
