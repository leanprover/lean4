// Lean compiler output
// Module: Std.Internal.Do.Order.Basic
// Imports: public import Init.Internal.Order
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_explicitBinders;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term_u22a4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Order_term_u22a4___closed__0 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__0_value;
static const lean_string_object l_Lean_Order_term_u22a4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Order_term_u22a4___closed__1 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__1_value;
static const lean_string_object l_Lean_Order_term_u22a4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term⊤"};
static const lean_object* l_Lean_Order_term_u22a4___closed__2 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__2_value;
static const lean_ctor_object l_Lean_Order_term_u22a4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term_u22a4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a4___closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term_u22a4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a4___closed__3_value_aux_1),((lean_object*)&l_Lean_Order_term_u22a4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 158, 127, 165, 41, 148, 243, 67)}};
static const lean_object* l_Lean_Order_term_u22a4___closed__3 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__3_value;
static const lean_string_object l_Lean_Order_term_u22a4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊤"};
static const lean_object* l_Lean_Order_term_u22a4___closed__4 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__4_value;
static const lean_ctor_object l_Lean_Order_term_u22a4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a4___closed__4_value)}};
static const lean_object* l_Lean_Order_term_u22a4___closed__5 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__5_value;
static const lean_ctor_object l_Lean_Order_term_u22a4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Order_term_u22a4___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__5_value)}};
static const lean_object* l_Lean_Order_term_u22a4___closed__6 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term_u22a4 = (const lean_object*)&l_Lean_Order_term_u22a4___closed__6_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__0_value;
static lean_once_cell_t l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__1;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 151, 114, 156, 65, 9, 103, 68)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__2_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__4_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__5 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__0_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term___u2293___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊓_"};
static const lean_object* l_Lean_Order_term___u2293___00__closed__0 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__0_value;
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Order_term___u2293___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 161, 18, 9, 245, 105, 116, 230)}};
static const lean_object* l_Lean_Order_term___u2293___00__closed__1 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__1_value;
static const lean_string_object l_Lean_Order_term___u2293___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Order_term___u2293___00__closed__2 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__2_value;
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2293___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Order_term___u2293___00__closed__3 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__3_value;
static const lean_string_object l_Lean_Order_term___u2293___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊓ "};
static const lean_object* l_Lean_Order_term___u2293___00__closed__4 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__4_value;
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__4_value)}};
static const lean_object* l_Lean_Order_term___u2293___00__closed__5 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__5_value;
static const lean_string_object l_Lean_Order_term___u2293___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Order_term___u2293___00__closed__6 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__6_value;
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2293___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Order_term___u2293___00__closed__7 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__7_value;
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__7_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Order_term___u2293___00__closed__8 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__8_value;
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__3_value),((lean_object*)&l_Lean_Order_term___u2293___00__closed__5_value),((lean_object*)&l_Lean_Order_term___u2293___00__closed__8_value)}};
static const lean_object* l_Lean_Order_term___u2293___00__closed__9 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__9_value;
static const lean_ctor_object l_Lean_Order_term___u2293___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__1_value),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2293___00__closed__9_value)}};
static const lean_object* l_Lean_Order_term___u2293___00__closed__10 = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term___u2293__ = (const lean_object*)&l_Lean_Order_term___u2293___00__closed__10_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__0_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__1_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__2_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_2),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__4_value;
static lean_once_cell_t l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__5;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 204, 102, 246, 245, 241, 10, 38)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__6 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__6_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__8 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__8_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__9 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__9_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__10 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__10_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__11 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__meet__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__meet__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term___u2294___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊔_"};
static const lean_object* l_Lean_Order_term___u2294___00__closed__0 = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__0_value;
static const lean_ctor_object l_Lean_Order_term___u2294___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term___u2294___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2294___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term___u2294___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2294___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Order_term___u2294___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 190, 198, 165, 181, 138, 196, 210)}};
static const lean_object* l_Lean_Order_term___u2294___00__closed__1 = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__1_value;
static const lean_string_object l_Lean_Order_term___u2294___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊔ "};
static const lean_object* l_Lean_Order_term___u2294___00__closed__2 = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__2_value;
static const lean_ctor_object l_Lean_Order_term___u2294___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2294___00__closed__2_value)}};
static const lean_object* l_Lean_Order_term___u2294___00__closed__3 = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__3_value;
static const lean_ctor_object l_Lean_Order_term___u2294___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__7_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Order_term___u2294___00__closed__4 = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__4_value;
static const lean_ctor_object l_Lean_Order_term___u2294___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__3_value),((lean_object*)&l_Lean_Order_term___u2294___00__closed__3_value),((lean_object*)&l_Lean_Order_term___u2294___00__closed__4_value)}};
static const lean_object* l_Lean_Order_term___u2294___00__closed__5 = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__5_value;
static const lean_ctor_object l_Lean_Order_term___u2294___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2294___00__closed__1_value),((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)&l_Lean_Order_term___u2294___00__closed__5_value)}};
static const lean_object* l_Lean_Order_term___u2294___00__closed__6 = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term___u2294__ = (const lean_object*)&l_Lean_Order_term___u2294___00__closed__6_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "join"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__0_value;
static lean_once_cell_t l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__1;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 169, 34, 86, 101, 136, 209, 77)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__2_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 209, 80, 138, 234, 64, 255, 112)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__4_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__5 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__join__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__join__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term_u2a05___x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term⨅_,_"};
static const lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__0 = (const lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__0_value;
static const lean_ctor_object l_Lean_Order_term_u2a05___x2c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term_u2a05___x2c___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term_u2a05___x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 157, 46, 249, 10, 212, 78, 125)}};
static const lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__1 = (const lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__1_value;
static const lean_string_object l_Lean_Order_term_u2a05___x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⨅ "};
static const lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__2 = (const lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__2_value;
static const lean_ctor_object l_Lean_Order_term_u2a05___x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__2_value)}};
static const lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__3 = (const lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__3_value;
static lean_once_cell_t l_Lean_Order_term_u2a05___x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__4;
static const lean_string_object l_Lean_Order_term_u2a05___x2c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__5 = (const lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__5_value;
static const lean_ctor_object l_Lean_Order_term_u2a05___x2c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__5_value)}};
static const lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__6 = (const lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__6_value;
static lean_once_cell_t l_Lean_Order_term_u2a05___x2c___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__7;
static const lean_ctor_object l_Lean_Order_term_u2a05___x2c___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__8 = (const lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__8_value;
static lean_once_cell_t l_Lean_Order_term_u2a05___x2c___00__closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__9;
static lean_once_cell_t l_Lean_Order_term_u2a05___x2c___00__closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a05___x2c___00__closed__10;
LEAN_EXPORT lean_object* l_Lean_Order_term_u2a05___x2c__;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__0_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 96, 105, 10, 16, 194, 128, 157)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Order_term_u2a06___x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term⨆_,_"};
static const lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__0 = (const lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__0_value;
static const lean_ctor_object l_Lean_Order_term_u2a06___x2c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term_u2a06___x2c___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term_u2a06___x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 181, 131, 200, 113, 90, 194)}};
static const lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__1 = (const lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__1_value;
static const lean_string_object l_Lean_Order_term_u2a06___x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⨆ "};
static const lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__2 = (const lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__2_value;
static const lean_ctor_object l_Lean_Order_term_u2a06___x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__2_value)}};
static const lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__3 = (const lean_object*)&l_Lean_Order_term_u2a06___x2c___00__closed__3_value;
static lean_once_cell_t l_Lean_Order_term_u2a06___x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__4;
static lean_once_cell_t l_Lean_Order_term_u2a06___x2c___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__5;
static lean_once_cell_t l_Lean_Order_term_u2a06___x2c___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__6;
static lean_once_cell_t l_Lean_Order_term_u2a06___x2c___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order_term_u2a06___x2c___00__closed__7;
LEAN_EXPORT lean_object* l_Lean_Order_term_u2a06___x2c__;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iSup"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__0_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 241, 153, 184, 251, 59, 2, 100)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_instPartialOrderProp__std;
LEAN_EXPORT lean_object* l_Lean_Order_instCompleteLatticeProp__std;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term⌜_⌝"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__0 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__0_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__1_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__1_value_aux_1),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 16, 241, 71, 126, 146, 187, 11)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__1 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__1_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌜"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__2 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__2_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__2_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__3 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__3_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__3_value),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__3_value),((lean_object*)&l_Lean_Order_term_u2a05___x2c___00__closed__8_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__4 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__4_value;
static const lean_string_object l_Lean_Order_term_u231c___u231d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌝"};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__5 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__5_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__5_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__6 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__6_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Order_term___u2293___00__closed__3_value),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__4_value),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__6_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__7 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__7_value;
static const lean_ctor_object l_Lean_Order_term_u231c___u231d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u231c___u231d___closed__7_value)}};
static const lean_object* l_Lean_Order_term_u231c___u231d___closed__8 = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Order_term_u231c___u231d = (const lean_object*)&l_Lean_Order_term_u231c___u231d___closed__8_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "CompleteLattice.ofProp"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__0 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__0_value;
static lean_once_cell_t l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__1;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__2 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__2_value;
static const lean_string_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__3 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 93, 31, 168, 215, 222, 197, 217)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 58, 144, 34, 172, 213, 101, 180)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__4 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__4_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Order_term_u22a4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Order_term_u22a4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__6 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__6_value;
static const lean_ctor_object l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__7 = (const lean_object*)&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__CompleteLattice__ofProp__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__CompleteLattice__ofProp__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__1(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__0));
v___x_18_ = l_String_toRawSubstring_x27(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1(lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = ((lean_object*)(l_Lean_Order_term_u22a4___closed__3));
v___x_35_ = l_Lean_Syntax_isOfKind(v_x_31_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_box(1);
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v_a_33_);
return v___x_37_;
}
else
{
lean_object* v_quotContext_38_; lean_object* v_currMacroScope_39_; lean_object* v_ref_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_quotContext_38_ = lean_ctor_get(v_a_32_, 1);
v_currMacroScope_39_ = lean_ctor_get(v_a_32_, 2);
v_ref_40_ = lean_ctor_get(v_a_32_, 5);
v___x_41_ = 0;
v___x_42_ = l_Lean_SourceInfo_fromRef(v_ref_40_, v___x_41_);
v___x_43_ = lean_obj_once(&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__1, &l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__1_once, _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__1);
v___x_44_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__2));
lean_inc(v_currMacroScope_39_);
lean_inc(v_quotContext_38_);
v___x_45_ = l_Lean_addMacroScope(v_quotContext_38_, v___x_44_, v_currMacroScope_39_);
v___x_46_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___closed__5));
v___x_47_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_47_, 0, v___x_42_);
lean_ctor_set(v___x_47_, 1, v___x_43_);
lean_ctor_set(v___x_47_, 2, v___x_45_);
lean_ctor_set(v___x_47_, 3, v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v_a_33_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1___boxed(lean_object* v_x_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u22a4__1(v_x_49_, v_a_50_, v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1(lean_object* v_x_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__1));
lean_inc(v_x_56_);
v___x_60_ = l_Lean_Syntax_isOfKind(v_x_56_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_x_56_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_a_58_);
return v___x_62_;
}
else
{
lean_object* v_ref_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_ref_63_ = l_Lean_replaceRef(v_x_56_, v_a_57_);
lean_dec(v_x_56_);
v___x_64_ = 0;
v___x_65_ = l_Lean_SourceInfo_fromRef(v_ref_63_, v___x_64_);
lean_dec(v_ref_63_);
v___x_66_ = ((lean_object*)(l_Lean_Order_term_u22a4___closed__3));
v___x_67_ = ((lean_object*)(l_Lean_Order_term_u22a4___closed__4));
lean_inc(v___x_65_);
v___x_68_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_65_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = l_Lean_Syntax_node1(v___x_65_, v___x_66_, v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_a_58_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___boxed(lean_object* v_x_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1(v_x_71_, v_a_72_, v_a_73_);
lean_dec(v_a_72_);
return v_res_74_;
}
}
static lean_object* _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__5(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__4));
v___x_111_ = l_String_toRawSubstring_x27(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1(lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__1));
lean_inc(v_x_127_);
v___x_131_ = l_Lean_Syntax_isOfKind(v_x_127_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_x_127_);
v___x_132_ = lean_box(1);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_a_129_);
return v___x_133_;
}
else
{
lean_object* v_quotContext_134_; lean_object* v_currMacroScope_135_; lean_object* v_ref_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_quotContext_134_ = lean_ctor_get(v_a_128_, 1);
v_currMacroScope_135_ = lean_ctor_get(v_a_128_, 2);
v_ref_136_ = lean_ctor_get(v_a_128_, 5);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = l_Lean_Syntax_getArg(v_x_127_, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(2u);
v___x_140_ = l_Lean_Syntax_getArg(v_x_127_, v___x_139_);
lean_dec(v_x_127_);
v___x_141_ = 0;
v___x_142_ = l_Lean_SourceInfo_fromRef(v_ref_136_, v___x_141_);
v___x_143_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3));
v___x_144_ = lean_obj_once(&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__5, &l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__5_once, _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__5);
v___x_145_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__6));
lean_inc(v_currMacroScope_135_);
lean_inc(v_quotContext_134_);
v___x_146_ = l_Lean_addMacroScope(v_quotContext_134_, v___x_145_, v_currMacroScope_135_);
v___x_147_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__9));
lean_inc_n(v___x_142_, 2);
v___x_148_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_148_, 0, v___x_142_);
lean_ctor_set(v___x_148_, 1, v___x_144_);
lean_ctor_set(v___x_148_, 2, v___x_146_);
lean_ctor_set(v___x_148_, 3, v___x_147_);
v___x_149_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__11));
v___x_150_ = l_Lean_Syntax_node2(v___x_142_, v___x_149_, v___x_138_, v___x_140_);
v___x_151_ = l_Lean_Syntax_node2(v___x_142_, v___x_143_, v___x_148_, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_a_129_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___boxed(lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1(v_x_153_, v_a_154_, v_a_155_);
lean_dec_ref(v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__meet__1(lean_object* v_x_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3));
lean_inc(v_x_157_);
v___x_161_ = l_Lean_Syntax_isOfKind(v_x_157_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_x_157_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_159_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Lean_Syntax_getArg(v_x_157_, v___x_164_);
v___x_166_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__1));
lean_inc(v___x_165_);
v___x_167_ = l_Lean_Syntax_isOfKind(v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v___x_165_);
lean_dec(v_x_157_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_a_159_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_157_, v___x_170_);
lean_dec(v_x_157_);
v___x_172_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_171_);
v___x_173_ = l_Lean_Syntax_matchesNull(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v___x_171_);
lean_dec(v___x_165_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_a_159_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_ref_178_; uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_176_ = l_Lean_Syntax_getArg(v___x_171_, v___x_164_);
v___x_177_ = l_Lean_Syntax_getArg(v___x_171_, v___x_170_);
lean_dec(v___x_171_);
v_ref_178_ = l_Lean_replaceRef(v___x_165_, v_a_158_);
lean_dec(v___x_165_);
v___x_179_ = 0;
v___x_180_ = l_Lean_SourceInfo_fromRef(v_ref_178_, v___x_179_);
lean_dec(v_ref_178_);
v___x_181_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__1));
v___x_182_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__4));
lean_inc(v___x_180_);
v___x_183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_180_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_Syntax_node3(v___x_180_, v___x_181_, v___x_176_, v___x_183_, v___x_177_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_159_);
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__meet__1___boxed(lean_object* v_x_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__meet__1(v_x_186_, v_a_187_, v_a_188_);
lean_dec(v_a_187_);
return v_res_189_;
}
}
static lean_object* _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__0));
v___x_212_ = l_String_toRawSubstring_x27(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1(lean_object* v_x_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Order_term___u2294___00__closed__1));
lean_inc(v_x_225_);
v___x_229_ = l_Lean_Syntax_isOfKind(v_x_225_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v_x_225_);
v___x_230_ = lean_box(1);
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_227_);
return v___x_231_;
}
else
{
lean_object* v_quotContext_232_; lean_object* v_currMacroScope_233_; lean_object* v_ref_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_quotContext_232_ = lean_ctor_get(v_a_226_, 1);
v_currMacroScope_233_ = lean_ctor_get(v_a_226_, 2);
v_ref_234_ = lean_ctor_get(v_a_226_, 5);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l_Lean_Syntax_getArg(v_x_225_, v___x_235_);
v___x_237_ = lean_unsigned_to_nat(2u);
v___x_238_ = l_Lean_Syntax_getArg(v_x_225_, v___x_237_);
lean_dec(v_x_225_);
v___x_239_ = 0;
v___x_240_ = l_Lean_SourceInfo_fromRef(v_ref_234_, v___x_239_);
v___x_241_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3));
v___x_242_ = lean_obj_once(&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__1, &l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__1_once, _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__1);
v___x_243_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__2));
lean_inc(v_currMacroScope_233_);
lean_inc(v_quotContext_232_);
v___x_244_ = l_Lean_addMacroScope(v_quotContext_232_, v___x_243_, v_currMacroScope_233_);
v___x_245_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___closed__5));
lean_inc_n(v___x_240_, 2);
v___x_246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_246_, 0, v___x_240_);
lean_ctor_set(v___x_246_, 1, v___x_242_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v___x_245_);
v___x_247_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__11));
v___x_248_ = l_Lean_Syntax_node2(v___x_240_, v___x_247_, v___x_236_, v___x_238_);
v___x_249_ = l_Lean_Syntax_node2(v___x_240_, v___x_241_, v___x_246_, v___x_248_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_a_227_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1___boxed(lean_object* v_x_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2294____1(v_x_251_, v_a_252_, v_a_253_);
lean_dec_ref(v_a_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__join__1(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3));
lean_inc(v_x_255_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_255_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_x_255_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = l_Lean_Syntax_getArg(v_x_255_, v___x_262_);
v___x_264_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__1));
lean_inc(v___x_263_);
v___x_265_ = l_Lean_Syntax_isOfKind(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v___x_263_);
lean_dec(v_x_255_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_a_257_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = l_Lean_Syntax_getArg(v_x_255_, v___x_268_);
lean_dec(v_x_255_);
v___x_270_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_269_);
v___x_271_ = l_Lean_Syntax_matchesNull(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v___x_269_);
lean_dec(v___x_263_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_a_257_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_ref_276_; uint8_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_274_ = l_Lean_Syntax_getArg(v___x_269_, v___x_262_);
v___x_275_ = l_Lean_Syntax_getArg(v___x_269_, v___x_268_);
lean_dec(v___x_269_);
v_ref_276_ = l_Lean_replaceRef(v___x_263_, v_a_256_);
lean_dec(v___x_263_);
v___x_277_ = 0;
v___x_278_ = l_Lean_SourceInfo_fromRef(v_ref_276_, v___x_277_);
lean_dec(v_ref_276_);
v___x_279_ = ((lean_object*)(l_Lean_Order_term___u2294___00__closed__1));
v___x_280_ = ((lean_object*)(l_Lean_Order_term___u2294___00__closed__2));
lean_inc(v___x_278_);
v___x_281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_278_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = l_Lean_Syntax_node3(v___x_278_, v___x_279_, v___x_274_, v___x_281_, v___x_275_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_a_257_);
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__join__1___boxed(lean_object* v_x_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__join__1(v_x_284_, v_a_285_, v_a_286_);
lean_dec(v_a_285_);
return v_res_287_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a05___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = l_Lean_explicitBinders;
v___x_297_ = ((lean_object*)(l_Lean_Order_term_u2a05___x2c___00__closed__3));
v___x_298_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__3));
v___x_299_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_ctor_set(v___x_299_, 2, v___x_296_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a05___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = ((lean_object*)(l_Lean_Order_term_u2a05___x2c___00__closed__6));
v___x_304_ = lean_obj_once(&l_Lean_Order_term_u2a05___x2c___00__closed__4, &l_Lean_Order_term_u2a05___x2c___00__closed__4_once, _init_l_Lean_Order_term_u2a05___x2c___00__closed__4);
v___x_305_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__3));
v___x_306_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_303_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a05___x2c___00__closed__9(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = ((lean_object*)(l_Lean_Order_term_u2a05___x2c___00__closed__8));
v___x_311_ = lean_obj_once(&l_Lean_Order_term_u2a05___x2c___00__closed__7, &l_Lean_Order_term_u2a05___x2c___00__closed__7_once, _init_l_Lean_Order_term_u2a05___x2c___00__closed__7);
v___x_312_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__3));
v___x_313_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_310_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a05___x2c___00__closed__10(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = lean_obj_once(&l_Lean_Order_term_u2a05___x2c___00__closed__9, &l_Lean_Order_term_u2a05___x2c___00__closed__9_once, _init_l_Lean_Order_term_u2a05___x2c___00__closed__9);
v___x_315_ = lean_unsigned_to_nat(1022u);
v___x_316_ = ((lean_object*)(l_Lean_Order_term_u2a05___x2c___00__closed__1));
v___x_317_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
lean_ctor_set(v___x_317_, 2, v___x_314_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a05___x2c__(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Lean_Order_term_u2a05___x2c___00__closed__10, &l_Lean_Order_term_u2a05___x2c___00__closed__10_once, _init_l_Lean_Order_term_u2a05___x2c___00__closed__10);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1(lean_object* v_x_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Order_term_u2a05___x2c___00__closed__1));
lean_inc(v_x_324_);
v___x_328_ = l_Lean_Syntax_isOfKind(v_x_324_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_x_324_);
v___x_329_ = lean_box(1);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_a_326_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = l_Lean_Syntax_getArg(v_x_324_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(3u);
v___x_334_ = l_Lean_Syntax_getArg(v_x_324_, v___x_333_);
lean_dec(v_x_324_);
v___x_335_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___closed__1));
v___x_336_ = l_Lean_expandExplicitBinders(v___x_335_, v___x_332_, v___x_334_, v_a_325_, v_a_326_);
lean_dec(v___x_332_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1___boxed(lean_object* v_x_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a05___x2c____1(v_x_337_, v_a_338_, v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a06___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_349_ = l_Lean_explicitBinders;
v___x_350_ = ((lean_object*)(l_Lean_Order_term_u2a06___x2c___00__closed__3));
v___x_351_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__3));
v___x_352_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
lean_ctor_set(v___x_352_, 2, v___x_349_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a06___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = ((lean_object*)(l_Lean_Order_term_u2a05___x2c___00__closed__6));
v___x_354_ = lean_obj_once(&l_Lean_Order_term_u2a06___x2c___00__closed__4, &l_Lean_Order_term_u2a06___x2c___00__closed__4_once, _init_l_Lean_Order_term_u2a06___x2c___00__closed__4);
v___x_355_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__3));
v___x_356_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_353_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a06___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = ((lean_object*)(l_Lean_Order_term_u2a05___x2c___00__closed__8));
v___x_358_ = lean_obj_once(&l_Lean_Order_term_u2a06___x2c___00__closed__5, &l_Lean_Order_term_u2a06___x2c___00__closed__5_once, _init_l_Lean_Order_term_u2a06___x2c___00__closed__5);
v___x_359_ = ((lean_object*)(l_Lean_Order_term___u2293___00__closed__3));
v___x_360_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
lean_ctor_set(v___x_360_, 2, v___x_357_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a06___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = lean_obj_once(&l_Lean_Order_term_u2a06___x2c___00__closed__6, &l_Lean_Order_term_u2a06___x2c___00__closed__6_once, _init_l_Lean_Order_term_u2a06___x2c___00__closed__6);
v___x_362_ = lean_unsigned_to_nat(1022u);
v___x_363_ = ((lean_object*)(l_Lean_Order_term_u2a06___x2c___00__closed__1));
v___x_364_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_361_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Order_term_u2a06___x2c__(void){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_Order_term_u2a06___x2c___00__closed__7, &l_Lean_Order_term_u2a06___x2c___00__closed__7_once, _init_l_Lean_Order_term_u2a06___x2c___00__closed__7);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1(lean_object* v_x_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Order_term_u2a06___x2c___00__closed__1));
lean_inc(v_x_371_);
v___x_375_ = l_Lean_Syntax_isOfKind(v_x_371_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_x_371_);
v___x_376_ = lean_box(1);
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_a_373_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = l_Lean_Syntax_getArg(v_x_371_, v___x_378_);
v___x_380_ = lean_unsigned_to_nat(3u);
v___x_381_ = l_Lean_Syntax_getArg(v_x_371_, v___x_380_);
lean_dec(v_x_371_);
v___x_382_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___closed__1));
v___x_383_ = l_Lean_expandExplicitBinders(v___x_382_, v___x_379_, v___x_381_, v_a_372_, v_a_373_);
lean_dec(v___x_379_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1___boxed(lean_object* v_x_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u2a06___x2c____1(v_x_384_, v_a_385_, v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_387_;
}
}
static lean_object* _init_l_Lean_Order_instPartialOrderProp__std(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Order_instCompleteLatticeProp__std(void){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__1(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__0));
v___x_416_ = l_String_toRawSubstring_x27(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1(lean_object* v_x_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__1));
lean_inc(v_x_433_);
v___x_437_ = l_Lean_Syntax_isOfKind(v_x_433_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_x_433_);
v___x_438_ = lean_box(1);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_a_435_);
return v___x_439_;
}
else
{
lean_object* v_quotContext_440_; lean_object* v_currMacroScope_441_; lean_object* v_ref_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_quotContext_440_ = lean_ctor_get(v_a_434_, 1);
v_currMacroScope_441_ = lean_ctor_get(v_a_434_, 2);
v_ref_442_ = lean_ctor_get(v_a_434_, 5);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = l_Lean_Syntax_getArg(v_x_433_, v___x_443_);
lean_dec(v_x_433_);
v___x_445_ = 0;
v___x_446_ = l_Lean_SourceInfo_fromRef(v_ref_442_, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3));
v___x_448_ = lean_obj_once(&l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__1, &l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__1_once, _init_l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__1);
v___x_449_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__4));
lean_inc(v_currMacroScope_441_);
lean_inc(v_quotContext_440_);
v___x_450_ = l_Lean_addMacroScope(v_quotContext_440_, v___x_449_, v_currMacroScope_441_);
v___x_451_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___closed__7));
lean_inc_n(v___x_446_, 2);
v___x_452_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_452_, 0, v___x_446_);
lean_ctor_set(v___x_452_, 1, v___x_448_);
lean_ctor_set(v___x_452_, 2, v___x_450_);
lean_ctor_set(v___x_452_, 3, v___x_451_);
v___x_453_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__11));
v___x_454_ = l_Lean_Syntax_node1(v___x_446_, v___x_453_, v___x_444_);
v___x_455_ = l_Lean_Syntax_node2(v___x_446_, v___x_447_, v___x_452_, v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_a_435_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1___boxed(lean_object* v_x_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term_u231c___u231d__1(v_x_457_, v_a_458_, v_a_459_);
lean_dec_ref(v_a_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__CompleteLattice__ofProp__1(lean_object* v_x_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______macroRules__Lean__Order__term___u2293____1___closed__3));
lean_inc(v_x_461_);
v___x_465_ = l_Lean_Syntax_isOfKind(v_x_461_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v_x_461_);
v___x_466_ = lean_box(0);
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_a_463_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l_Lean_Syntax_getArg(v_x_461_, v___x_468_);
v___x_470_ = ((lean_object*)(l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__top__1___closed__1));
lean_inc(v___x_469_);
v___x_471_ = l_Lean_Syntax_isOfKind(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v___x_469_);
lean_dec(v_x_461_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_a_463_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = l_Lean_Syntax_getArg(v_x_461_, v___x_474_);
lean_dec(v_x_461_);
lean_inc(v___x_475_);
v___x_476_ = l_Lean_Syntax_matchesNull(v___x_475_, v___x_474_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v___x_475_);
lean_dec(v___x_469_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_a_463_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v_ref_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_479_ = l_Lean_Syntax_getArg(v___x_475_, v___x_468_);
lean_dec(v___x_475_);
v_ref_480_ = l_Lean_replaceRef(v___x_469_, v_a_462_);
lean_dec(v___x_469_);
v___x_481_ = 0;
v___x_482_ = l_Lean_SourceInfo_fromRef(v_ref_480_, v___x_481_);
lean_dec(v_ref_480_);
v___x_483_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__1));
v___x_484_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__2));
lean_inc_n(v___x_482_, 2);
v___x_485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_482_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = ((lean_object*)(l_Lean_Order_term_u231c___u231d___closed__5));
v___x_487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_482_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_Syntax_node3(v___x_482_, v___x_483_, v___x_485_, v___x_479_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_a_463_);
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__CompleteLattice__ofProp__1___boxed(lean_object* v_x_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Order___aux__Std__Internal__Do__Order__Basic______unexpand__Lean__Order__CompleteLattice__ofProp__1(v_x_490_, v_a_491_, v_a_492_);
lean_dec(v_a_491_);
return v_res_493_;
}
}
lean_object* runtime_initialize_Init_Internal_Order(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Internal_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Order_instPartialOrderProp__std = _init_l_Lean_Order_instPartialOrderProp__std();
lean_mark_persistent(l_Lean_Order_instPartialOrderProp__std);
l_Lean_Order_instCompleteLatticeProp__std = _init_l_Lean_Order_instCompleteLatticeProp__std();
lean_mark_persistent(l_Lean_Order_instCompleteLatticeProp__std);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Order_term_u2a05___x2c__ = _init_l_Lean_Order_term_u2a05___x2c__();
lean_mark_persistent(l_Lean_Order_term_u2a05___x2c__);
l_Lean_Order_term_u2a06___x2c__ = _init_l_Lean_Order_term_u2a06___x2c__();
lean_mark_persistent(l_Lean_Order_term_u2a06___x2c__);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Internal_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Internal_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Order_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
