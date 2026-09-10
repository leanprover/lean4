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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term___u2291___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__0 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__1 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__1_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊑_"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__2 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__2_value;
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term___u2291___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term___u2291___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2291___00__closed__3_value_aux_1),((lean_object*)&l_Lean_Order_term___u2291___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(63, 167, 88, 175, 201, 86, 126, 172)}};
static const lean_object* l_Lean_Order_term___u2291___00__closed__3 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__3_value;
static const lean_string_object l_Lean_Order_term___u2291___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Order_term___u2291___00__closed__4 = (const lean_object*)&l_Lean_Order_term___u2291___00__closed__4_value;
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
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2291___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_2),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "PartialOrder.rel"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4_value;
static lean_once_cell_t l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value;
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value;
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
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value;
static const lean_ctor_object l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1_value;
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
static lean_once_cell_t l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderUnit;
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOUnit;
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeUnit;
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Order_Example_findF(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4));
v___x_40_ = l_String_toRawSubstring_x27(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1(lean_object* v_x_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Order_term___u2291___00__closed__3));
lean_inc(v_x_60_);
v___x_64_ = l_Lean_Syntax_isOfKind(v_x_60_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_x_60_);
v___x_65_ = lean_box(1);
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_a_62_);
return v___x_66_;
}
else
{
lean_object* v_quotContext_67_; lean_object* v_currMacroScope_68_; lean_object* v_ref_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_quotContext_67_ = lean_ctor_get(v_a_61_, 1);
v_currMacroScope_68_ = lean_ctor_get(v_a_61_, 2);
v_ref_69_ = lean_ctor_get(v_a_61_, 5);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l_Lean_Syntax_getArg(v_x_60_, v___x_70_);
v___x_72_ = lean_unsigned_to_nat(2u);
v___x_73_ = l_Lean_Syntax_getArg(v_x_60_, v___x_72_);
lean_dec(v_x_60_);
v___x_74_ = 0;
v___x_75_ = l_Lean_SourceInfo_fromRef(v_ref_69_, v___x_74_);
v___x_76_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3));
v___x_77_ = lean_obj_once(&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5, &l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5_once, _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5);
v___x_78_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8));
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
v___x_79_ = l_Lean_addMacroScope(v_quotContext_67_, v___x_78_, v_currMacroScope_68_);
v___x_80_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11));
lean_inc_n(v___x_75_, 2);
v___x_81_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_81_, 0, v___x_75_);
lean_ctor_set(v___x_81_, 1, v___x_77_);
lean_ctor_set(v___x_81_, 2, v___x_79_);
lean_ctor_set(v___x_81_, 3, v___x_80_);
v___x_82_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13));
v___x_83_ = l_Lean_Syntax_node2(v___x_75_, v___x_82_, v___x_71_, v___x_73_);
v___x_84_ = l_Lean_Syntax_node2(v___x_75_, v___x_76_, v___x_81_, v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v_a_62_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___boxed(lean_object* v_x_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1(v_x_86_, v_a_87_, v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3));
lean_inc(v_x_93_);
v___x_97_ = l_Lean_Syntax_isOfKind(v_x_93_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_x_93_);
v___x_98_ = lean_box(0);
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_a_95_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = l_Lean_Syntax_getArg(v_x_93_, v___x_100_);
v___x_102_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1));
lean_inc(v___x_101_);
v___x_103_ = l_Lean_Syntax_isOfKind(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v___x_101_);
lean_dec(v_x_93_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_a_95_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = l_Lean_Syntax_getArg(v_x_93_, v___x_106_);
lean_dec(v_x_93_);
v___x_108_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_107_);
v___x_109_ = l_Lean_Syntax_matchesNull(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v___x_107_);
lean_dec(v___x_101_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_95_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_ref_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_112_ = l_Lean_Syntax_getArg(v___x_107_, v___x_100_);
v___x_113_ = l_Lean_Syntax_getArg(v___x_107_, v___x_106_);
lean_dec(v___x_107_);
v_ref_114_ = l_Lean_replaceRef(v___x_101_, v_a_94_);
lean_dec(v___x_101_);
v___x_115_ = 0;
v___x_116_ = l_Lean_SourceInfo_fromRef(v_ref_114_, v___x_115_);
lean_dec(v_ref_114_);
v___x_117_ = ((lean_object*)(l_Lean_Order_term___u2291___00__closed__3));
v___x_118_ = ((lean_object*)(l_Lean_Order_term___u2291___00__closed__6));
lean_inc(v___x_116_);
v___x_119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = l_Lean_Syntax_node3(v___x_116_, v___x_117_, v___x_112_, v___x_119_, v___x_113_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_a_95_);
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___boxed(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1(v_x_122_, v_a_123_, v_a_124_);
lean_dec(v_a_123_);
return v_res_125_;
}
}
static lean_object* _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0));
v___x_141_ = l_String_toRawSubstring_x27(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1(lean_object* v_x_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Order_term_u22a5___closed__1));
v___x_158_ = l_Lean_Syntax_isOfKind(v_x_154_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_box(1);
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_a_156_);
return v___x_160_;
}
else
{
lean_object* v_quotContext_161_; lean_object* v_currMacroScope_162_; lean_object* v_ref_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_quotContext_161_ = lean_ctor_get(v_a_155_, 1);
v_currMacroScope_162_ = lean_ctor_get(v_a_155_, 2);
v_ref_163_ = lean_ctor_get(v_a_155_, 5);
v___x_164_ = 0;
v___x_165_ = l_Lean_SourceInfo_fromRef(v_ref_163_, v___x_164_);
v___x_166_ = lean_obj_once(&l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1, &l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1_once, _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1);
v___x_167_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2));
lean_inc(v_currMacroScope_162_);
lean_inc(v_quotContext_161_);
v___x_168_ = l_Lean_addMacroScope(v_quotContext_161_, v___x_167_, v_currMacroScope_162_);
v___x_169_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5));
v___x_170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_165_);
lean_ctor_set(v___x_170_, 1, v___x_166_);
lean_ctor_set(v___x_170_, 2, v___x_168_);
lean_ctor_set(v___x_170_, 3, v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_a_156_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___boxed(lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1(v_x_172_, v_a_173_, v_a_174_);
lean_dec_ref(v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1(lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1));
lean_inc(v_x_176_);
v___x_180_ = l_Lean_Syntax_isOfKind(v_x_176_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_x_176_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_178_);
return v___x_182_;
}
else
{
lean_object* v_ref_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_ref_183_ = l_Lean_replaceRef(v_x_176_, v_a_177_);
lean_dec(v_x_176_);
v___x_184_ = 0;
v___x_185_ = l_Lean_SourceInfo_fromRef(v_ref_183_, v___x_184_);
lean_dec(v_ref_183_);
v___x_186_ = ((lean_object*)(l_Lean_Order_term_u22a5___closed__1));
v___x_187_ = ((lean_object*)(l_Lean_Order_term_u22a5___closed__2));
lean_inc(v___x_185_);
v___x_188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_185_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = l_Lean_Syntax_node1(v___x_185_, v___x_186_, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_178_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1___boxed(lean_object* v_x_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1(v_x_191_, v_a_192_, v_a_193_);
lean_dec(v_a_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___boxed(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Order_instOrderPi(v_00_u03b1_199_, v_00_u03b2_200_, v_inst_201_);
lean_dec_ref(v_inst_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_inst_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___boxed(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Order_instCCPOPi(v_00_u03b1_207_, v_00_u03b2_208_, v_inst_209_);
lean_dec_ref(v_inst_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___boxed(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Order_instCompleteLatticePi(v_00_u03b1_215_, v_00_u03b2_216_, v_inst_217_);
lean_dec_ref(v_inst_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_inst_221_, lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_inst_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_box(0);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd(lean_object* v_00_u03b1_229_, lean_object* v_00_u03b2_230_, lean_object* v_inst_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProd(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_inst_236_, lean_object* v_inst_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOProd(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_inst_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(0);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeProd(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_inst_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_box(0);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Order_instPartialOrderUnit(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_box(0);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Order_instCCPOUnit(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_box(0);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Order_instCompleteLatticeUnit(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___redArg(lean_object* v_x_252_){
_start:
{
lean_inc(v_x_252_);
return v_x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___redArg___boxed(lean_object* v_x_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Order_FlatOrder_mk___redArg(v_x_253_);
lean_dec(v_x_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk(lean_object* v_00_u03b1_255_, lean_object* v_b_256_, lean_object* v_x_257_){
_start:
{
lean_inc(v_x_257_);
return v_x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___boxed(lean_object* v_00_u03b1_258_, lean_object* v_b_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Order_FlatOrder_mk(v_00_u03b1_258_, v_b_259_, v_x_260_);
lean_dec(v_x_260_);
lean_dec(v_b_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___redArg(lean_object* v_x_262_){
_start:
{
lean_inc(v_x_262_);
return v_x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___redArg___boxed(lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Order_FlatOrder_inner___redArg(v_x_263_);
lean_dec(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner(lean_object* v_00_u03b1_265_, lean_object* v_b_266_, lean_object* v_x_267_){
_start:
{
lean_inc(v_x_267_);
return v_x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___boxed(lean_object* v_00_u03b1_268_, lean_object* v_b_269_, lean_object* v_x_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Order_FlatOrder_inner(v_00_u03b1_268_, v_b_269_, v_x_270_);
lean_dec(v_x_270_);
lean_dec(v_b_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder(lean_object* v_00_u03b1_272_, lean_object* v_b_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_box(0);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___boxed(lean_object* v_00_u03b1_275_, lean_object* v_b_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Order_FlatOrder_instOrder(v_00_u03b1_275_, v_b_276_);
lean_dec(v_b_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO(lean_object* v_00_u03b1_278_, lean_object* v_b_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___boxed(lean_object* v_00_u03b1_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Order_FlatOrder_instCCPO(v_00_u03b1_281_, v_b_282_);
lean_dec(v_b_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption(lean_object* v_00_u03b1_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(0);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption(lean_object* v_00_u03b1_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT___redArg(lean_object* v_inst_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_apply_1(v_inst_288_, lean_box(0));
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT(lean_object* v_m_290_, lean_object* v_00_u03b5_291_, lean_object* v_00_u03b1_292_, lean_object* v_inst_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_apply_1(v_inst_293_, lean_box(0));
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT___redArg(lean_object* v_inst_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_apply_1(v_inst_295_, lean_box(0));
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT(lean_object* v_m_297_, lean_object* v_00_u03b5_298_, lean_object* v_00_u03b1_299_, lean_object* v_inst_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_apply_1(v_inst_300_, lean_box(0));
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT___redArg(lean_object* v_inst_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_apply_1(v_inst_302_, lean_box(0));
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT(lean_object* v_m_304_, lean_object* v_00_u03b1_305_, lean_object* v_inst_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_apply_1(v_inst_306_, lean_box(0));
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT___redArg(lean_object* v_inst_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_apply_1(v_inst_308_, lean_box(0));
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT(lean_object* v_m_310_, lean_object* v_00_u03b1_311_, lean_object* v_inst_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_apply_1(v_inst_312_, lean_box(0));
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT(lean_object* v_m_314_, lean_object* v_00_u03c1_315_, lean_object* v_00_u03b1_316_, lean_object* v_inst_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT(lean_object* v_m_319_, lean_object* v_00_u03c1_320_, lean_object* v_00_u03b1_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27(lean_object* v_m_324_, lean_object* v_00_u03c9_325_, lean_object* v_00_u03c3_326_, lean_object* v_00_u03b1_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27(lean_object* v_m_330_, lean_object* v_00_u03c9_331_, lean_object* v_00_u03c3_332_, lean_object* v_00_u03b1_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(0);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT(lean_object* v_m_336_, lean_object* v_00_u03c3_337_, lean_object* v_00_u03b1_338_, lean_object* v_inst_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___boxed(lean_object* v_m_341_, lean_object* v_00_u03c3_342_, lean_object* v_00_u03b1_343_, lean_object* v_inst_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Order_instPartialOrderStateT(v_m_341_, v_00_u03c3_342_, v_00_u03b1_343_, v_inst_344_);
lean_dec_ref(v_inst_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT(lean_object* v_m_346_, lean_object* v_00_u03c3_347_, lean_object* v_00_u03b1_348_, lean_object* v_inst_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(0);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___boxed(lean_object* v_m_351_, lean_object* v_00_u03c3_352_, lean_object* v_00_u03b1_353_, lean_object* v_inst_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Order_instCCPOStateT(v_m_351_, v_00_u03c3_352_, v_00_u03b1_353_, v_inst_354_);
lean_dec_ref(v_inst_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty(lean_object* v_00_u03b5_356_, lean_object* v_00_u03c3_357_, lean_object* v_00_u03b1_358_, lean_object* v_inst_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_box(0);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter___redArg(lean_object* v_x_361_, lean_object* v_h__1_362_, lean_object* v_h__2_363_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; 
lean_dec(v_h__2_363_);
v_a_364_ = lean_ctor_get(v_x_361_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v_x_361_, 1);
v___x_365_ = lean_apply_2(v_h__1_362_, v_a_364_, lean_box(0));
return v___x_365_;
}
else
{
lean_object* v_a_366_; lean_object* v___x_367_; 
lean_dec(v_h__1_362_);
v_a_366_ = lean_ctor_get(v_x_361_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v_x_361_, 1);
v___x_367_ = lean_apply_2(v_h__2_363_, v_a_366_, lean_box(0));
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter(lean_object* v_00_u03b5_368_, lean_object* v_00_u03c3_369_, lean_object* v_00_u03b1_370_, lean_object* v_motive_371_, lean_object* v_x_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
lean_dec(v_h__2_374_);
v_a_375_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v_x_372_, 1);
v___x_376_ = lean_apply_2(v_h__1_373_, v_a_375_, lean_box(0));
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v___x_378_; 
lean_dec(v_h__1_373_);
v_a_377_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v_x_372_, 1);
v___x_378_ = lean_apply_2(v_h__2_374_, v_a_377_, lean_box(0));
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty(lean_object* v_00_u03b5_379_, lean_object* v_00_u03b1_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_box(0);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOIO(lean_object* v_00_u03b1_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Order_ImplicationOrder_instOrder(void){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Order_ImplicationOrder_instCompleteLattice(void){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Order_ReverseImplicationOrder_instOrder(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Order_ReverseImplicationOrder_instCompleteLattice(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_Example_findF(lean_object* v_P_389_, lean_object* v_rec_390_, lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
lean_inc(v_x_391_);
v___x_392_ = lean_apply_1(v_P_389_, v_x_391_);
v___x_393_ = lean_unbox(v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_x_391_, v___x_394_);
lean_dec(v_x_391_);
v___x_396_ = lean_apply_1(v_rec_390_, v___x_395_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; 
lean_dec_ref(v_rec_390_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_x_391_);
return v___x_397_;
}
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
lean_object* runtime_initialize_Init_System_ST(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Order_instPartialOrderUnit = _init_l_Lean_Order_instPartialOrderUnit();
lean_mark_persistent(l_Lean_Order_instPartialOrderUnit);
l_Lean_Order_instCCPOUnit = _init_l_Lean_Order_instCCPOUnit();
lean_mark_persistent(l_Lean_Order_instCCPOUnit);
l_Lean_Order_instCompleteLatticeUnit = _init_l_Lean_Order_instCompleteLatticeUnit();
lean_mark_persistent(l_Lean_Order_instCompleteLatticeUnit);
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
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Internal_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Internal_Order_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
