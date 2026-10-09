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
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProd___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOProd___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOProd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeProd___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeProd___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOIO___redArg();
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOIO___redArg___boxed(lean_object*);
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
lean_object* l_Lean_Order_instOrderPi___redArg(){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
LEAN_EXPORT void l_Lean_Order_instOrderPi___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_197_;
v_res_197_ = l_Lean_Order_instOrderPi___redArg();
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___redArg___boxed(lean_object* v___dummy_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Order_instOrderPi___redArg();
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_inst_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instOrderPi___boxed(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Order_instOrderPi(v_00_u03b1_204_, v_00_u03b2_205_, v_inst_206_);
lean_dec_ref(v_inst_206_);
return v_res_207_;
}
}
lean_object* l_Lean_Order_instCCPOPi___redArg(){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOPi___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_210_;
v_res_210_ = l_Lean_Order_instCCPOPi___redArg();
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___redArg___boxed(lean_object* v___dummy_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Order_instCCPOPi___redArg();
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi(lean_object* v_00_u03b1_213_, lean_object* v_00_u03b2_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPi___boxed(lean_object* v_00_u03b1_217_, lean_object* v_00_u03b2_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Order_instCCPOPi(v_00_u03b1_217_, v_00_u03b2_218_, v_inst_219_);
lean_dec_ref(v_inst_219_);
return v_res_220_;
}
}
lean_object* l_Lean_Order_instCompleteLatticePi___redArg(){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
LEAN_EXPORT void l_Lean_Order_instCompleteLatticePi___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_223_;
v_res_223_ = l_Lean_Order_instCompleteLatticePi___redArg();
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___redArg___boxed(lean_object* v___dummy_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Order_instCompleteLatticePi___redArg();
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_inst_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_box(0);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePi___boxed(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Order_instCompleteLatticePi(v_00_u03b1_230_, v_00_u03b2_231_, v_inst_232_);
lean_dec_ref(v_inst_232_);
return v_res_233_;
}
}
lean_object* l_Lean_Order_instPartialOrderPProd___redArg(){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_box(0);
return v___x_235_;
}
}
LEAN_EXPORT void l_Lean_Order_instPartialOrderPProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_236_;
v_res_236_ = l_Lean_Order_instPartialOrderPProd___redArg();
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd___redArg___boxed(lean_object* v___dummy_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Order_instPartialOrderPProd___redArg();
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderPProd(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_inst_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(0);
return v___x_243_;
}
}
lean_object* l_Lean_Order_instCCPOPProd___redArg(){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_box(0);
return v___x_245_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOPProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_246_;
v_res_246_ = l_Lean_Order_instCCPOPProd___redArg();
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd___redArg___boxed(lean_object* v___dummy_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Order_instCCPOPProd___redArg();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOPProd(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_inst_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_box(0);
return v___x_253_;
}
}
lean_object* l_Lean_Order_instCompleteLatticePProd___redArg(){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_box(0);
return v___x_255_;
}
}
LEAN_EXPORT void l_Lean_Order_instCompleteLatticePProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_256_;
v_res_256_ = l_Lean_Order_instCompleteLatticePProd___redArg();
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd___redArg___boxed(lean_object* v___dummy_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Order_instCompleteLatticePProd___redArg();
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticePProd(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_inst_261_, lean_object* v_inst_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
lean_object* l_Lean_Order_instPartialOrderProd___redArg(){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_box(0);
return v___x_265_;
}
}
LEAN_EXPORT void l_Lean_Order_instPartialOrderProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_266_;
v_res_266_ = l_Lean_Order_instPartialOrderProd___redArg();
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProd___redArg___boxed(lean_object* v___dummy_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Order_instPartialOrderProd___redArg();
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProd(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_inst_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_box(0);
return v___x_273_;
}
}
lean_object* l_Lean_Order_instCCPOProd___redArg(){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_box(0);
return v___x_275_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_276_;
v_res_276_ = l_Lean_Order_instCCPOProd___redArg();
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOProd___redArg___boxed(lean_object* v___dummy_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Order_instCCPOProd___redArg();
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOProd(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_inst_281_, lean_object* v_inst_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_box(0);
return v___x_283_;
}
}
lean_object* l_Lean_Order_instCompleteLatticeProd___redArg(){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(0);
return v___x_285_;
}
}
LEAN_EXPORT void l_Lean_Order_instCompleteLatticeProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_286_;
v_res_286_ = l_Lean_Order_instCompleteLatticeProd___redArg();
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeProd___redArg___boxed(lean_object* v___dummy_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Order_instCompleteLatticeProd___redArg();
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeProd(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_inst_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Order_instPartialOrderUnit(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(0);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Order_instCCPOUnit(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Order_instCompleteLatticeUnit(void){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___redArg(lean_object* v_x_297_){
_start:
{
lean_inc(v_x_297_);
return v_x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___redArg___boxed(lean_object* v_x_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Order_FlatOrder_mk___redArg(v_x_298_);
lean_dec(v_x_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk(lean_object* v_00_u03b1_300_, lean_object* v_b_301_, lean_object* v_x_302_){
_start:
{
lean_inc(v_x_302_);
return v_x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_mk___boxed(lean_object* v_00_u03b1_303_, lean_object* v_b_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Order_FlatOrder_mk(v_00_u03b1_303_, v_b_304_, v_x_305_);
lean_dec(v_x_305_);
lean_dec(v_b_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___redArg(lean_object* v_x_307_){
_start:
{
lean_inc(v_x_307_);
return v_x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___redArg___boxed(lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Order_FlatOrder_inner___redArg(v_x_308_);
lean_dec(v_x_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner(lean_object* v_00_u03b1_310_, lean_object* v_b_311_, lean_object* v_x_312_){
_start:
{
lean_inc(v_x_312_);
return v_x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_inner___boxed(lean_object* v_00_u03b1_313_, lean_object* v_b_314_, lean_object* v_x_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Order_FlatOrder_inner(v_00_u03b1_313_, v_b_314_, v_x_315_);
lean_dec(v_x_315_);
lean_dec(v_b_314_);
return v_res_316_;
}
}
lean_object* l_Lean_Order_FlatOrder_instOrder___redArg(){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
LEAN_EXPORT void l_Lean_Order_FlatOrder_instOrder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_319_;
v_res_319_ = l_Lean_Order_FlatOrder_instOrder___redArg();
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___redArg___boxed(lean_object* v___dummy_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Order_FlatOrder_instOrder___redArg();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder(lean_object* v_00_u03b1_322_, lean_object* v_b_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instOrder___boxed(lean_object* v_00_u03b1_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Order_FlatOrder_instOrder(v_00_u03b1_325_, v_b_326_);
lean_dec(v_b_326_);
return v_res_327_;
}
}
lean_object* l_Lean_Order_FlatOrder_instCCPO___redArg(){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
}
LEAN_EXPORT void l_Lean_Order_FlatOrder_instCCPO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_330_;
v_res_330_ = l_Lean_Order_FlatOrder_instCCPO___redArg();
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___redArg___boxed(lean_object* v___dummy_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Order_FlatOrder_instCCPO___redArg();
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO(lean_object* v_00_u03b1_333_, lean_object* v_b_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(0);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FlatOrder_instCCPO___boxed(lean_object* v_00_u03b1_336_, lean_object* v_b_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Order_FlatOrder_instCCPO(v_00_u03b1_336_, v_b_337_);
lean_dec(v_b_337_);
return v_res_338_;
}
}
lean_object* l_Lean_Order_instPartialOrderOption___redArg(){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
}
LEAN_EXPORT void l_Lean_Order_instPartialOrderOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_341_;
v_res_341_ = l_Lean_Order_instPartialOrderOption___redArg();
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption___redArg___boxed(lean_object* v___dummy_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Order_instPartialOrderOption___redArg();
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOption(lean_object* v_00_u03b1_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
}
lean_object* l_Lean_Order_instCCPOOption___redArg(){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_box(0);
return v___x_347_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_348_;
v_res_348_ = l_Lean_Order_instCCPOOption___redArg();
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption___redArg___boxed(lean_object* v___dummy_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Order_instCCPOOption___redArg();
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOption(lean_object* v_00_u03b1_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT___redArg(lean_object* v_inst_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_apply_1(v_inst_353_, lean_box(0));
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderExceptT(lean_object* v_m_355_, lean_object* v_00_u03b5_356_, lean_object* v_00_u03b1_357_, lean_object* v_inst_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_apply_1(v_inst_358_, lean_box(0));
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT___redArg(lean_object* v_inst_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_1(v_inst_360_, lean_box(0));
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOExceptT(lean_object* v_m_362_, lean_object* v_00_u03b5_363_, lean_object* v_00_u03b1_364_, lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_apply_1(v_inst_365_, lean_box(0));
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT___redArg(lean_object* v_inst_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_apply_1(v_inst_367_, lean_box(0));
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderOptionT(lean_object* v_m_369_, lean_object* v_00_u03b1_370_, lean_object* v_inst_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_apply_1(v_inst_371_, lean_box(0));
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT___redArg(lean_object* v_inst_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_apply_1(v_inst_373_, lean_box(0));
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOOptionT(lean_object* v_m_375_, lean_object* v_00_u03b1_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_apply_1(v_inst_377_, lean_box(0));
return v___x_378_;
}
}
lean_object* l_Lean_Order_instPartialOrderReaderT___redArg(){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
}
LEAN_EXPORT void l_Lean_Order_instPartialOrderReaderT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_381_;
v_res_381_ = l_Lean_Order_instPartialOrderReaderT___redArg();
stack->m_obj
 = v_res_381_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT___redArg___boxed(lean_object* v___dummy_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Order_instPartialOrderReaderT___redArg();
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderReaderT(lean_object* v_m_384_, lean_object* v_00_u03c1_385_, lean_object* v_00_u03b1_386_, lean_object* v_inst_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
lean_object* l_Lean_Order_instCCPOReaderT___redArg(){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_box(0);
return v___x_390_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOReaderT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_391_;
v_res_391_ = l_Lean_Order_instCCPOReaderT___redArg();
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT___redArg___boxed(lean_object* v___dummy_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Order_instCCPOReaderT___redArg();
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOReaderT(lean_object* v_m_394_, lean_object* v_00_u03c1_395_, lean_object* v_00_u03b1_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_box(0);
return v___x_398_;
}
}
lean_object* l_Lean_Order_instPartialOrderStateRefT_x27___redArg(){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
return v___x_400_;
}
}
LEAN_EXPORT void l_Lean_Order_instPartialOrderStateRefT_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_401_;
v_res_401_ = l_Lean_Order_instPartialOrderStateRefT_x27___redArg();
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27___redArg___boxed(lean_object* v___dummy_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Order_instPartialOrderStateRefT_x27___redArg();
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateRefT_x27(lean_object* v_m_404_, lean_object* v_00_u03c9_405_, lean_object* v_00_u03c3_406_, lean_object* v_00_u03b1_407_, lean_object* v_inst_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
return v___x_409_;
}
}
lean_object* l_Lean_Order_instCCPOStateRefT_x27___redArg(){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOStateRefT_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_412_;
v_res_412_ = l_Lean_Order_instCCPOStateRefT_x27___redArg();
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27___redArg___boxed(lean_object* v___dummy_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Order_instCCPOStateRefT_x27___redArg();
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateRefT_x27(lean_object* v_m_415_, lean_object* v_00_u03c9_416_, lean_object* v_00_u03c3_417_, lean_object* v_00_u03b1_418_, lean_object* v_inst_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_box(0);
return v___x_420_;
}
}
lean_object* l_Lean_Order_instPartialOrderStateT___redArg(){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
LEAN_EXPORT void l_Lean_Order_instPartialOrderStateT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_423_;
v_res_423_ = l_Lean_Order_instPartialOrderStateT___redArg();
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___redArg___boxed(lean_object* v___dummy_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Order_instPartialOrderStateT___redArg();
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT(lean_object* v_m_426_, lean_object* v_00_u03c3_427_, lean_object* v_00_u03b1_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderStateT___boxed(lean_object* v_m_431_, lean_object* v_00_u03c3_432_, lean_object* v_00_u03b1_433_, lean_object* v_inst_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Order_instPartialOrderStateT(v_m_431_, v_00_u03c3_432_, v_00_u03b1_433_, v_inst_434_);
lean_dec_ref(v_inst_434_);
return v_res_435_;
}
}
lean_object* l_Lean_Order_instCCPOStateT___redArg(){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_box(0);
return v___x_437_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOStateT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_438_;
v_res_438_ = l_Lean_Order_instCCPOStateT___redArg();
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___redArg___boxed(lean_object* v___dummy_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Order_instCCPOStateT___redArg();
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT(lean_object* v_m_441_, lean_object* v_00_u03c3_442_, lean_object* v_00_u03b1_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_box(0);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOStateT___boxed(lean_object* v_m_446_, lean_object* v_00_u03c3_447_, lean_object* v_00_u03b1_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Order_instCCPOStateT(v_m_446_, v_00_u03c3_447_, v_00_u03b1_448_, v_inst_449_);
lean_dec_ref(v_inst_449_);
return v_res_450_;
}
}
lean_object* l_Lean_Order_instCCPOESTOfNonempty___redArg(){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOESTOfNonempty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_453_;
v_res_453_ = l_Lean_Order_instCCPOESTOfNonempty___redArg();
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty___redArg___boxed(lean_object* v___dummy_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Order_instCCPOESTOfNonempty___redArg();
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOESTOfNonempty(lean_object* v_00_u03b5_456_, lean_object* v_00_u03c3_457_, lean_object* v_00_u03b1_458_, lean_object* v_inst_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter___redArg(lean_object* v_x_461_, lean_object* v_h__1_462_, lean_object* v_h__2_463_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
lean_dec(v_h__2_463_);
v_a_464_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v_x_461_, 1);
v___x_465_ = lean_apply_2(v_h__1_462_, v_a_464_, lean_box(0));
return v___x_465_;
}
else
{
lean_object* v_a_466_; lean_object* v___x_467_; 
lean_dec(v_h__1_462_);
v_a_466_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v_x_461_, 1);
v___x_467_ = lean_apply_2(v_h__2_463_, v_a_466_, lean_box(0));
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter(lean_object* v_00_u03b5_468_, lean_object* v_00_u03c3_469_, lean_object* v_00_u03b1_470_, lean_object* v_motive_471_, lean_object* v_x_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; 
lean_dec(v_h__2_474_);
v_a_475_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v_x_472_, 1);
v___x_476_ = lean_apply_2(v_h__1_473_, v_a_475_, lean_box(0));
return v___x_476_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_478_; 
lean_dec(v_h__1_473_);
v_a_477_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v_x_472_, 1);
v___x_478_ = lean_apply_2(v_h__2_474_, v_a_477_, lean_box(0));
return v___x_478_;
}
}
}
lean_object* l_Lean_Order_instCCPOEIOOfNonempty___redArg(){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_box(0);
return v___x_480_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOEIOOfNonempty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_481_;
v_res_481_ = l_Lean_Order_instCCPOEIOOfNonempty___redArg();
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty___redArg___boxed(lean_object* v___dummy_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Order_instCCPOEIOOfNonempty___redArg();
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOEIOOfNonempty(lean_object* v_00_u03b5_484_, lean_object* v_00_u03b1_485_, lean_object* v_inst_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
return v___x_487_;
}
}
lean_object* l_Lean_Order_instCCPOIO___redArg(){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = lean_box(0);
return v___x_489_;
}
}
LEAN_EXPORT void l_Lean_Order_instCCPOIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_490_;
v_res_490_ = l_Lean_Order_instCCPOIO___redArg();
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOIO___redArg___boxed(lean_object* v___dummy_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Order_instCCPOIO___redArg();
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_instCCPOIO(lean_object* v_00_u03b1_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(0);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Order_ImplicationOrder_instOrder(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_box(0);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Order_ImplicationOrder_instCompleteLattice(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_box(0);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Order_ReverseImplicationOrder_instOrder(void){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = lean_box(0);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Order_ReverseImplicationOrder_instCompleteLattice(void){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_box(0);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_Example_findF(lean_object* v_P_499_, lean_object* v_rec_500_, lean_object* v_x_501_){
_start:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
lean_inc(v_x_501_);
v___x_502_ = lean_apply_1(v_P_499_, v_x_501_);
v___x_503_ = lean_unbox(v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_x_501_, v___x_504_);
lean_dec(v_x_501_);
v___x_506_ = lean_apply_1(v_rec_500_, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
lean_dec_ref(v_rec_500_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v_x_501_);
return v___x_507_;
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
