// Lean compiler output
// Module: Std.Internal.Do.Frame
// Imports: public import Std.Internal.Do.Assertion
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term___u21e8___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__0 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__0_value;
static const lean_string_object l_Lean_Order_term___u21e8___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__1 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__1_value;
static const lean_string_object l_Lean_Order_term___u21e8___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⇨_"};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__2 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__2_value;
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u21e8___00__closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u21e8___00__closed__3_value_aux_1),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 23, 169, 55, 3, 249, 158, 171)}};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__3 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__3_value;
static const lean_string_object l_Lean_Order_term___u21e8___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__4 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__4_value;
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__5 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__5_value;
static const lean_string_object l_Lean_Order_term___u21e8___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⇨ "};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__6 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__6_value;
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term___u21e8___00__closed__6_value)}};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__7 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__7_value;
static const lean_string_object l_Lean_Order_term___u21e8___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__8 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__8_value;
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__9 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__9_value;
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Order_term___u21e8___00__closed__9_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__10 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__10_value;
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term___u21e8___00__closed__5_value),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__7_value),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__10_value)}};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__11 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__11_value;
static const lean_ctor_object l_Lean_Order_term___u21e8___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Order_term___u21e8___00__closed__3_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__11_value)}};
static const lean_object* l_Lean_Order_term___u21e8___00__closed__12 = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term___u21e8__ = (const lean_object*)&l_Lean_Order_term___u21e8___00__closed__12_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_2),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value;
static lean_once_cell_t l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 93, 163, 74, 45, 235, 252, 9)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_0),((lean_object*)&l_Lean_Order_term___u21e8___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4));
v___x_40_ = l_String_toRawSubstring_x27(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1(lean_object* v_x_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Order_term___u21e8___00__closed__3));
lean_inc(v_x_56_);
v___x_60_ = l_Lean_Syntax_isOfKind(v_x_56_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_x_56_);
v___x_61_ = lean_box(1);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_a_58_);
return v___x_62_;
}
else
{
lean_object* v_quotContext_63_; lean_object* v_currMacroScope_64_; lean_object* v_ref_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_quotContext_63_ = lean_ctor_get(v_a_57_, 1);
v_currMacroScope_64_ = lean_ctor_get(v_a_57_, 2);
v_ref_65_ = lean_ctor_get(v_a_57_, 5);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = l_Lean_Syntax_getArg(v_x_56_, v___x_66_);
v___x_68_ = lean_unsigned_to_nat(2u);
v___x_69_ = l_Lean_Syntax_getArg(v_x_56_, v___x_68_);
lean_dec(v_x_56_);
v___x_70_ = 0;
v___x_71_ = l_Lean_SourceInfo_fromRef(v_ref_65_, v___x_70_);
v___x_72_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3));
v___x_73_ = lean_obj_once(&l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5, &l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5_once, _init_l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5);
v___x_74_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6));
lean_inc(v_currMacroScope_64_);
lean_inc(v_quotContext_63_);
v___x_75_ = l_Lean_addMacroScope(v_quotContext_63_, v___x_74_, v_currMacroScope_64_);
v___x_76_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9));
lean_inc_n(v___x_71_, 2);
v___x_77_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_77_, 0, v___x_71_);
lean_ctor_set(v___x_77_, 1, v___x_73_);
lean_ctor_set(v___x_77_, 2, v___x_75_);
lean_ctor_set(v___x_77_, 3, v___x_76_);
v___x_78_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11));
v___x_79_ = l_Lean_Syntax_node2(v___x_71_, v___x_78_, v___x_67_, v___x_69_);
v___x_80_ = l_Lean_Syntax_node2(v___x_71_, v___x_72_, v___x_77_, v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_a_58_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___boxed(lean_object* v_x_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1(v_x_82_, v_a_83_, v_a_84_);
lean_dec_ref(v_a_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1(lean_object* v_x_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3));
lean_inc(v_x_89_);
v___x_93_ = l_Lean_Syntax_isOfKind(v_x_89_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_x_89_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_a_91_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = l_Lean_Syntax_getArg(v_x_89_, v___x_96_);
v___x_98_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1));
lean_inc(v___x_97_);
v___x_99_ = l_Lean_Syntax_isOfKind(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v___x_97_);
lean_dec(v_x_89_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_91_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = l_Lean_Syntax_getArg(v_x_89_, v___x_102_);
lean_dec(v_x_89_);
v___x_104_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_103_);
v___x_105_ = l_Lean_Syntax_matchesNull(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v___x_103_);
lean_dec(v___x_97_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_a_91_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_ref_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_108_ = l_Lean_Syntax_getArg(v___x_103_, v___x_96_);
v___x_109_ = l_Lean_Syntax_getArg(v___x_103_, v___x_102_);
lean_dec(v___x_103_);
v_ref_110_ = l_Lean_replaceRef(v___x_97_, v_a_90_);
lean_dec(v___x_97_);
v___x_111_ = 0;
v___x_112_ = l_Lean_SourceInfo_fromRef(v_ref_110_, v___x_111_);
lean_dec(v_ref_110_);
v___x_113_ = ((lean_object*)(l_Lean_Order_term___u21e8___00__closed__3));
v___x_114_ = ((lean_object*)(l_Lean_Order_term___u21e8___00__closed__6));
lean_inc(v___x_112_);
v___x_115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_112_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = l_Lean_Syntax_node3(v___x_112_, v___x_113_, v___x_108_, v___x_115_, v___x_109_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_a_91_);
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___boxed(lean_object* v_x_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1(v_x_118_, v_a_119_, v_a_120_);
lean_dec(v_a_119_);
return v_res_121_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_Assertion(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Frame(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Frame(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_Assertion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Frame(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Frame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Frame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Frame(builtin);
}
#ifdef __cplusplus
}
#endif
