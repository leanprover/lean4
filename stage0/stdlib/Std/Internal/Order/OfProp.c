// Lean compiler output
// Module: Std.Internal.Order.OfProp
// Imports: public import Std.Internal.Order.Lemmas public import Init.ByCases import Init.Classical
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__0 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__0_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__1 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__1_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term⌜_⌝"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__2 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__2_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__3_value_aux_1),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 16, 241, 71, 126, 146, 187, 11)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__3 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__3_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__4 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__4_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__5 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__5_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌜"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__6 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__6_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__6_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__7 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__7_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__8 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__8_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__9 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__9_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__10 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__10_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__5_value),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__7_value),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__10_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__11 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__11_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌝"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__12 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__12_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__12_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__13 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__13_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__5_value),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__11_value),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__13_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__14 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__14_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__14_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__15 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__15_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term_u231c___u231d = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__15_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__0_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__1_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__2_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "CompleteLattice.ofProp"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__4_value;
static lean_once_cell_t l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__5;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__6 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__6_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__7 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__7_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(115, 93, 31, 168, 215, 222, 197, 217)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(87, 58, 144, 34, 172, 213, 101, 180)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__8 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__8_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__10 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__10_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__11 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__11_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__12 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__12_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__13 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__0_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__5(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__4));
v___x_46_ = l_String_toRawSubstring_x27(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1(lean_object* v_x_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__3));
lean_inc(v_x_66_);
v___x_70_ = l_Lean_Syntax_isOfKind(v_x_66_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_x_66_);
v___x_71_ = lean_box(1);
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_a_68_);
return v___x_72_;
}
else
{
lean_object* v_quotContext_73_; lean_object* v_currMacroScope_74_; lean_object* v_ref_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_quotContext_73_ = lean_ctor_get(v_a_67_, 1);
v_currMacroScope_74_ = lean_ctor_get(v_a_67_, 2);
v_ref_75_ = lean_ctor_get(v_a_67_, 5);
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = l_Lean_Syntax_getArg(v_x_66_, v___x_76_);
lean_dec(v_x_66_);
v___x_78_ = 0;
v___x_79_ = l_Lean_SourceInfo_fromRef(v_ref_75_, v___x_78_);
v___x_80_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3));
v___x_81_ = lean_obj_once(&l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__5, &l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_once, _init_l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__5);
v___x_82_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__8));
lean_inc(v_currMacroScope_74_);
lean_inc(v_quotContext_73_);
v___x_83_ = l_Lean_addMacroScope(v_quotContext_73_, v___x_82_, v_currMacroScope_74_);
v___x_84_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__11));
lean_inc_n(v___x_79_, 2);
v___x_85_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_85_, 0, v___x_79_);
lean_ctor_set(v___x_85_, 1, v___x_81_);
lean_ctor_set(v___x_85_, 2, v___x_83_);
lean_ctor_set(v___x_85_, 3, v___x_84_);
v___x_86_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__13));
v___x_87_ = l_Lean_Syntax_node1(v___x_79_, v___x_86_, v___x_77_);
v___x_88_ = l_Lean_Syntax_node2(v___x_79_, v___x_80_, v___x_85_, v___x_87_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_a_68_);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___boxed(lean_object* v_x_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1(v_x_90_, v_a_91_, v_a_92_);
lean_dec_ref(v_a_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Order__OfProp______macroRules__Lean__Order__term_u231c___u231d__1___closed__3));
lean_inc(v_x_97_);
v___x_101_ = l_Lean_Syntax_isOfKind(v_x_97_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_x_97_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_a_99_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_97_, v___x_104_);
v___x_106_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___closed__1));
lean_inc(v___x_105_);
v___x_107_ = l_Lean_Syntax_isOfKind(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v___x_105_);
lean_dec(v_x_97_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_a_99_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = l_Lean_Syntax_getArg(v_x_97_, v___x_110_);
lean_dec(v_x_97_);
lean_inc(v___x_111_);
v___x_112_ = l_Lean_Syntax_matchesNull(v___x_111_, v___x_110_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v___x_111_);
lean_dec(v___x_105_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_99_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v_ref_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_115_ = l_Lean_Syntax_getArg(v___x_111_, v___x_104_);
lean_dec(v___x_111_);
v_ref_116_ = l_Lean_replaceRef(v___x_105_, v_a_98_);
lean_dec(v___x_105_);
v___x_117_ = 0;
v___x_118_ = l_Lean_SourceInfo_fromRef(v_ref_116_, v___x_117_);
lean_dec(v_ref_116_);
v___x_119_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__3));
v___x_120_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__6));
lean_inc_n(v___x_118_, 2);
v___x_121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_118_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__12));
v___x_123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_118_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = l_Lean_Syntax_node3(v___x_118_, v___x_119_, v___x_121_, v___x_115_, v___x_123_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_99_);
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1___boxed(lean_object* v_x_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Order___aux__Std__Internal__Order__OfProp______unexpand__Lean__Order__CompleteLattice__ofProp__1(v_x_126_, v_a_127_, v_a_128_);
lean_dec(v_a_127_);
return v_res_129_;
}
}
lean_object* runtime_initialize_Std_Internal_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Order_OfProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Order_OfProp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Order_OfProp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_OfProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Order_OfProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Order_OfProp(builtin);
}
#ifdef __cplusplus
}
#endif
