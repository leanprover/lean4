// Lean compiler output
// Module: Std.Do.WP.Basic
// Imports: public import Std.Do.PredTrans
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
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_PredTrans_pure___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Do_PredTrans_pushOption___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Std_Do_PredTrans_pushExcept___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Std_Do_PredTrans_pushArg___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_PredTrans_pure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_PredTrans_bind___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 11, .m_data = "termWp⟦_:_⟧"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_0),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_1),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 96, 4, 176, 128, 111, 85, 188)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = "wp⟦"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value),((lean_object*)(((size_t)(10) << 1) | 1))}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19_value;
static const lean_string_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟧"};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19_value),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22_value;
static const lean_ctor_object l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22_value)}};
static const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23_value;
LEAN_EXPORT const lean_object* l_Std_Do_termWp_u27e6___x3a___u27e7 = (const lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value_aux_0),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "WP.wp"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(46, 215, 163, 54, 140, 34, 198, 104)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(252, 184, 149, 68, 51, 92, 194, 92)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_0),((lean_object*)&l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(209, 91, 166, 6, 71, 210, 197, 93)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(111, 2, 24, 48, 222, 174, 4, 243)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32_value;
static const lean_string_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34;
static const lean_ctor_object l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(171, 239, 198, 100, 229, 128, 136, 1)}};
static const lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35 = (const lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Do_unexpandWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(13, 5, 49, 23, 162, 70, 143, 74)}};
static const lean_object* l_Std_Do_unexpandWP___closed__0 = (const lean_object*)&l_Std_Do_unexpandWP___closed__0_value;
static lean_once_cell_t l_Std_Do_unexpandWP___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_unexpandWP___closed__1;
LEAN_EXPORT lean_object* l_Std_Do_unexpandWP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_unexpandWP___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Id_instWP___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Do_Id_instWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_Id_instWP___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_Id_instWP___closed__0 = (const lean_object*)&l_Std_Do_Id_instWP___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Do_Id_instWP = (const lean_object*)&l_Std_Do_Id_instWP___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Do_EStateM_instWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_EStateM_instWP___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_EStateM_instWP___closed__0 = (const lean_object*)&l_Std_Do_EStateM_instWP___closed__0_value;
static const lean_closure_object l_Std_Do_EStateM_instWP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_EStateM_instWP___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Do_EStateM_instWP___closed__0_value)} };
static const lean_object* l_Std_Do_EStateM_instWP___closed__1 = (const lean_object*)&l_Std_Do_EStateM_instWP___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_State_instWP___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_State_instWP___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Do_State_instWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_State_instWP___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_State_instWP___closed__0 = (const lean_object*)&l_Std_Do_State_instWP___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_State_instWP(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWP___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWP___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Do_Reader_instWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_Reader_instWP___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Do_Reader_instWP___closed__0 = (const lean_object*)&l_Std_Do_Reader_instWP___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWP(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Except_instWP___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Except_instWP___aux__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Do_Except_instWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_Except_instWP___aux__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Do_Except_instWP___closed__0 = (const lean_object*)&l_Std_Do_Except_instWP___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_Except_instWP(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Option_instWP___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Option_instWP___aux__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Do_Option_instWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_Option_instWP___aux__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_Option_instWP___closed__0 = (const lean_object*)&l_Std_Do_Option_instWP___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Do_Option_instWP = (const lean_object*)&l_Std_Do_Option_instWP___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12));
v___x_83_ = l_String_toRawSubstring_x27(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19));
v___x_100_ = l_String_toRawSubstring_x27(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33));
v___x_130_ = l_String_toRawSubstring_x27(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1(lean_object* v_x_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3));
lean_inc(v_x_133_);
v___x_137_ = l_Lean_Syntax_isOfKind(v_x_133_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_x_133_);
v___x_138_ = lean_box(1);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_135_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = l_Lean_Syntax_getArg(v_x_133_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_144_ = l_Lean_Syntax_getArg(v_x_133_, v___x_143_);
lean_dec(v_x_133_);
lean_inc(v___x_144_);
v___x_145_ = l_Lean_Syntax_matchesNull(v___x_144_, v___x_140_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; 
lean_inc(v___x_144_);
v___x_146_ = l_Lean_Syntax_matchesNull(v___x_144_, v___x_143_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v___x_144_);
lean_dec(v___x_142_);
v___x_147_ = lean_box(1);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_a_135_);
return v___x_148_;
}
else
{
lean_object* v_quotContext_149_; lean_object* v_currMacroScope_150_; lean_object* v_ref_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_quotContext_149_ = lean_ctor_get(v_a_134_, 1);
v_currMacroScope_150_ = lean_ctor_get(v_a_134_, 2);
v_ref_151_ = lean_ctor_get(v_a_134_, 5);
v___x_152_ = l_Lean_Syntax_getArg(v___x_144_, v___x_141_);
lean_dec(v___x_144_);
v___x_153_ = l_Lean_SourceInfo_fromRef(v_ref_151_, v___x_145_);
v___x_154_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4));
v___x_155_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6));
v___x_156_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8));
v___x_157_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9));
lean_inc_n(v___x_153_, 14);
v___x_158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_153_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11));
v___x_160_ = lean_obj_once(&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13, &l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13);
v___x_161_ = lean_box(0);
lean_inc_n(v_currMacroScope_150_, 3);
lean_inc_n(v_quotContext_149_, 3);
v___x_162_ = l_Lean_addMacroScope(v_quotContext_149_, v___x_161_, v_currMacroScope_150_);
v___x_163_ = lean_box(0);
v___x_164_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16));
v___x_165_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_165_, 0, v___x_153_);
lean_ctor_set(v___x_165_, 1, v___x_160_);
lean_ctor_set(v___x_165_, 2, v___x_162_);
lean_ctor_set(v___x_165_, 3, v___x_164_);
v___x_166_ = l_Lean_Syntax_node1(v___x_153_, v___x_159_, v___x_165_);
v___x_167_ = l_Lean_Syntax_node2(v___x_153_, v___x_156_, v___x_158_, v___x_166_);
v___x_168_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18));
v___x_169_ = lean_obj_once(&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20, &l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20_once, _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20);
v___x_170_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23));
v___x_171_ = l_Lean_addMacroScope(v_quotContext_149_, v___x_170_, v_currMacroScope_150_);
v___x_172_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26));
v___x_173_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_173_, 0, v___x_153_);
lean_ctor_set(v___x_173_, 1, v___x_169_);
lean_ctor_set(v___x_173_, 2, v___x_171_);
lean_ctor_set(v___x_173_, 3, v___x_172_);
v___x_174_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_175_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30));
v___x_176_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14));
v___x_177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_153_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = l_Lean_Syntax_node1(v___x_153_, v___x_174_, v___x_152_);
v___x_179_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31));
v___x_180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_153_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
lean_inc_ref(v___x_180_);
lean_inc(v___x_167_);
v___x_181_ = l_Lean_Syntax_node5(v___x_153_, v___x_175_, v___x_167_, v___x_142_, v___x_177_, v___x_178_, v___x_180_);
v___x_182_ = l_Lean_Syntax_node1(v___x_153_, v___x_174_, v___x_181_);
v___x_183_ = l_Lean_Syntax_node2(v___x_153_, v___x_168_, v___x_173_, v___x_182_);
v___x_184_ = l_Lean_Syntax_node3(v___x_153_, v___x_155_, v___x_167_, v___x_183_, v___x_180_);
v___x_185_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32));
v___x_186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_153_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_obj_once(&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34, &l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34_once, _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34);
v___x_188_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35));
v___x_189_ = l_Lean_addMacroScope(v_quotContext_149_, v___x_188_, v_currMacroScope_150_);
v___x_190_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_190_, 0, v___x_153_);
lean_ctor_set(v___x_190_, 1, v___x_187_);
lean_ctor_set(v___x_190_, 2, v___x_189_);
lean_ctor_set(v___x_190_, 3, v___x_163_);
v___x_191_ = l_Lean_Syntax_node3(v___x_153_, v___x_154_, v___x_184_, v___x_186_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_a_135_);
return v___x_192_;
}
}
else
{
lean_object* v_quotContext_193_; lean_object* v_currMacroScope_194_; lean_object* v_ref_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v___x_144_);
v_quotContext_193_ = lean_ctor_get(v_a_134_, 1);
v_currMacroScope_194_ = lean_ctor_get(v_a_134_, 2);
v_ref_195_ = lean_ctor_get(v_a_134_, 5);
v___x_196_ = 0;
v___x_197_ = l_Lean_SourceInfo_fromRef(v_ref_195_, v___x_196_);
v___x_198_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4));
v___x_199_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6));
v___x_200_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8));
v___x_201_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9));
lean_inc_n(v___x_197_, 11);
v___x_202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_197_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11));
v___x_204_ = lean_obj_once(&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13, &l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13);
v___x_205_ = lean_box(0);
lean_inc_n(v_currMacroScope_194_, 3);
lean_inc_n(v_quotContext_193_, 3);
v___x_206_ = l_Lean_addMacroScope(v_quotContext_193_, v___x_205_, v_currMacroScope_194_);
v___x_207_ = lean_box(0);
v___x_208_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16));
v___x_209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_209_, 0, v___x_197_);
lean_ctor_set(v___x_209_, 1, v___x_204_);
lean_ctor_set(v___x_209_, 2, v___x_206_);
lean_ctor_set(v___x_209_, 3, v___x_208_);
v___x_210_ = l_Lean_Syntax_node1(v___x_197_, v___x_203_, v___x_209_);
v___x_211_ = l_Lean_Syntax_node2(v___x_197_, v___x_200_, v___x_202_, v___x_210_);
v___x_212_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18));
v___x_213_ = lean_obj_once(&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20, &l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20_once, _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20);
v___x_214_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23));
v___x_215_ = l_Lean_addMacroScope(v_quotContext_193_, v___x_214_, v_currMacroScope_194_);
v___x_216_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26));
v___x_217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_217_, 0, v___x_197_);
lean_ctor_set(v___x_217_, 1, v___x_213_);
lean_ctor_set(v___x_217_, 2, v___x_215_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
v___x_218_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_219_ = l_Lean_Syntax_node1(v___x_197_, v___x_218_, v___x_142_);
v___x_220_ = l_Lean_Syntax_node2(v___x_197_, v___x_212_, v___x_217_, v___x_219_);
v___x_221_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31));
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_197_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_Lean_Syntax_node3(v___x_197_, v___x_199_, v___x_211_, v___x_220_, v___x_222_);
v___x_224_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32));
v___x_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_197_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_obj_once(&l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34, &l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34_once, _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34);
v___x_227_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35));
v___x_228_ = l_Lean_addMacroScope(v_quotContext_193_, v___x_227_, v_currMacroScope_194_);
v___x_229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_229_, 0, v___x_197_);
lean_ctor_set(v___x_229_, 1, v___x_226_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
lean_ctor_set(v___x_229_, 3, v___x_207_);
v___x_230_ = l_Lean_Syntax_node3(v___x_197_, v___x_198_, v___x_223_, v___x_225_, v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_135_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___boxed(lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1(v_x_232_, v_a_233_, v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_235_;
}
}
static lean_object* _init_l_Std_Do_unexpandWP___closed__1(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Array_mkArray0(lean_box(0));
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_unexpandWP(lean_object* v_x_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18));
lean_inc(v_x_239_);
v___x_243_ = l_Lean_Syntax_isOfKind(v_x_239_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_x_239_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_a_241_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = l_Lean_Syntax_getArg(v_x_239_, v___x_246_);
lean_dec(v_x_239_);
lean_inc(v___x_247_);
v___x_248_ = l_Lean_Syntax_matchesNull(v___x_247_, v___x_246_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___x_247_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_a_241_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Lean_Syntax_getArg(v___x_247_, v___x_251_);
lean_dec(v___x_247_);
lean_inc(v___x_252_);
v___x_253_ = l_Lean_Syntax_isOfKind(v___x_252_, v___x_242_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_252_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_241_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = l_Lean_Syntax_getArg(v___x_252_, v___x_251_);
v___x_257_ = ((lean_object*)(l_Std_Do_unexpandWP___closed__0));
v___x_258_ = l_Lean_Syntax_matchesIdent(v___x_256_, v___x_257_);
lean_dec(v___x_256_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v___x_252_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_a_241_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = l_Lean_Syntax_getArg(v___x_252_, v___x_246_);
lean_dec(v___x_252_);
lean_inc(v___x_261_);
v___x_262_ = l_Lean_Syntax_matchesNull(v___x_261_, v___x_246_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v___x_261_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_a_241_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = l_Lean_Syntax_getArg(v___x_261_, v___x_251_);
lean_dec(v___x_261_);
v___x_266_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30));
lean_inc(v___x_265_);
v___x_267_ = l_Lean_Syntax_isOfKind(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_268_ = l_Lean_SourceInfo_fromRef(v_a_240_, v___x_267_);
v___x_269_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3));
v___x_270_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6));
lean_inc_n(v___x_268_, 3);
v___x_271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_268_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_273_ = lean_obj_once(&l_Std_Do_unexpandWP___closed__1, &l_Std_Do_unexpandWP___closed__1_once, _init_l_Std_Do_unexpandWP___closed__1);
v___x_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_274_, 0, v___x_268_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_273_);
v___x_275_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20));
v___x_276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_268_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = l_Lean_Syntax_node4(v___x_268_, v___x_269_, v___x_271_, v___x_265_, v___x_274_, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_241_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = l_Lean_Syntax_getArg(v___x_265_, v___x_251_);
v___x_280_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8));
lean_inc(v___x_279_);
v___x_281_ = l_Lean_Syntax_isOfKind(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v___x_279_);
v___x_282_ = l_Lean_SourceInfo_fromRef(v_a_240_, v___x_281_);
v___x_283_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3));
v___x_284_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6));
lean_inc_n(v___x_282_, 3);
v___x_285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_282_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_287_ = lean_obj_once(&l_Std_Do_unexpandWP___closed__1, &l_Std_Do_unexpandWP___closed__1_once, _init_l_Std_Do_unexpandWP___closed__1);
v___x_288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_288_, 0, v___x_282_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
lean_ctor_set(v___x_288_, 2, v___x_287_);
v___x_289_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20));
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_282_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_Syntax_node4(v___x_282_, v___x_283_, v___x_285_, v___x_265_, v___x_288_, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_a_241_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = l_Lean_Syntax_getArg(v___x_279_, v___x_246_);
lean_dec(v___x_279_);
v___x_294_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11));
lean_inc(v___x_293_);
v___x_295_ = l_Lean_Syntax_isOfKind(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v___x_293_);
v___x_296_ = l_Lean_SourceInfo_fromRef(v_a_240_, v___x_295_);
v___x_297_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3));
v___x_298_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6));
lean_inc_n(v___x_296_, 3);
v___x_299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_296_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_301_ = lean_obj_once(&l_Std_Do_unexpandWP___closed__1, &l_Std_Do_unexpandWP___closed__1_once, _init_l_Std_Do_unexpandWP___closed__1);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_296_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
v___x_303_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20));
v___x_304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_296_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_Syntax_node4(v___x_296_, v___x_297_, v___x_299_, v___x_265_, v___x_302_, v___x_304_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_a_241_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = l_Lean_Syntax_getArg(v___x_293_, v___x_251_);
lean_dec(v___x_293_);
v___x_308_ = lean_box(0);
v___x_309_ = l_Lean_Syntax_matchesIdent(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_310_ = l_Lean_SourceInfo_fromRef(v_a_240_, v___x_309_);
v___x_311_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3));
v___x_312_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6));
lean_inc_n(v___x_310_, 3);
v___x_313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_310_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_315_ = lean_obj_once(&l_Std_Do_unexpandWP___closed__1, &l_Std_Do_unexpandWP___closed__1_once, _init_l_Std_Do_unexpandWP___closed__1);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_310_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
v___x_317_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20));
v___x_318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_310_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_Syntax_node4(v___x_310_, v___x_311_, v___x_313_, v___x_265_, v___x_316_, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_241_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(3u);
v___x_322_ = l_Lean_Syntax_getArg(v___x_265_, v___x_321_);
lean_inc(v___x_322_);
v___x_323_ = l_Lean_Syntax_matchesNull(v___x_322_, v___x_246_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v___x_322_);
v___x_324_ = l_Lean_SourceInfo_fromRef(v_a_240_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3));
v___x_326_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6));
lean_inc_n(v___x_324_, 3);
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_324_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_329_ = lean_obj_once(&l_Std_Do_unexpandWP___closed__1, &l_Std_Do_unexpandWP___closed__1_once, _init_l_Std_Do_unexpandWP___closed__1);
v___x_330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_330_, 0, v___x_324_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_329_);
v___x_331_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20));
v___x_332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_324_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = l_Lean_Syntax_node4(v___x_324_, v___x_325_, v___x_327_, v___x_265_, v___x_330_, v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_a_241_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_335_ = l_Lean_Syntax_getArg(v___x_265_, v___x_246_);
lean_dec(v___x_265_);
v___x_336_ = l_Lean_Syntax_getArg(v___x_322_, v___x_251_);
lean_dec(v___x_322_);
v___x_337_ = 0;
v___x_338_ = l_Lean_SourceInfo_fromRef(v_a_240_, v___x_337_);
v___x_339_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3));
v___x_340_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6));
lean_inc_n(v___x_338_, 4);
v___x_341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_338_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = ((lean_object*)(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28));
v___x_343_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_338_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Syntax_node2(v___x_338_, v___x_342_, v___x_344_, v___x_336_);
v___x_346_ = ((lean_object*)(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20));
v___x_347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_338_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = l_Lean_Syntax_node4(v___x_338_, v___x_339_, v___x_341_, v___x_335_, v___x_345_, v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_241_);
return v___x_349_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_unexpandWP___boxed(lean_object* v_x_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Do_unexpandWP(v_x_350_, v_a_351_, v_a_352_);
lean_dec(v_a_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Id_instWP___lam__0(lean_object* v_00_u03b1_354_, lean_object* v_x_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_Do_PredTrans_pure___redArg___lam__0(v_x_355_, v___y_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___redArg___lam__0(lean_object* v_x_360_, lean_object* v_inst_361_, lean_object* v_s_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_apply_1(v_x_360_, v_s_362_);
v___x_365_ = lean_apply_3(v_inst_361_, lean_box(0), v___x_364_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___redArg___lam__1(lean_object* v_inst_366_, lean_object* v_00_u03b1_367_, lean_object* v_x_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___f_370_; lean_object* v___x_371_; 
v___f_370_ = lean_alloc_closure((void*)(l_Std_Do_StateT_instWP___redArg___lam__0), 4, 2);
lean_closure_set(v___f_370_, 0, v_x_368_);
lean_closure_set(v___f_370_, 1, v_inst_366_);
v___x_371_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushArg___redArg___lam__1), 3, 2);
lean_closure_set(v___x_371_, 0, v___f_370_);
lean_closure_set(v___x_371_, 1, v___y_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___redArg(lean_object* v_inst_372_){
_start:
{
lean_object* v___f_373_; 
v___f_373_ = lean_alloc_closure((void*)(l_Std_Do_StateT_instWP___redArg___lam__1), 4, 1);
lean_closure_set(v___f_373_, 0, v_inst_372_);
return v___f_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP(lean_object* v_m_374_, lean_object* v_ps_375_, lean_object* v_00_u03c3_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v___f_378_; 
v___f_378_ = lean_alloc_closure((void*)(l_Std_Do_StateT_instWP___redArg___lam__1), 4, 1);
lean_closure_set(v___f_378_, 0, v_inst_377_);
return v___f_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWP___boxed(lean_object* v_m_379_, lean_object* v_ps_380_, lean_object* v_00_u03c3_381_, lean_object* v_inst_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Do_StateT_instWP(v_m_379_, v_ps_380_, v_00_u03c3_381_, v_inst_382_);
lean_dec(v_ps_380_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__0(lean_object* v_s_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_x_385_);
lean_ctor_set(v___x_386_, 1, v_s_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__1(lean_object* v_x_387_, lean_object* v_inst_388_, lean_object* v_ps_389_, lean_object* v_s_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_inc(v_s_390_);
v___f_392_ = lean_alloc_closure((void*)(l_Std_Do_ReaderT_instWP___redArg___lam__0), 2, 1);
lean_closure_set(v___f_392_, 0, v_s_390_);
v___x_393_ = lean_apply_1(v_x_387_, v_s_390_);
v___x_394_ = lean_apply_2(v_inst_388_, lean_box(0), v___x_393_);
v___x_395_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pure___boxed), 3, 2);
lean_closure_set(v___x_395_, 0, v_ps_389_);
lean_closure_set(v___x_395_, 1, lean_box(0));
v___x_396_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_396_, 0, lean_box(0));
lean_closure_set(v___x_396_, 1, lean_box(0));
lean_closure_set(v___x_396_, 2, lean_box(0));
lean_closure_set(v___x_396_, 3, v___x_395_);
lean_closure_set(v___x_396_, 4, v___f_392_);
v___x_397_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_396_, v___x_394_, v___y_391_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__2(lean_object* v_inst_398_, lean_object* v_ps_399_, lean_object* v_00_u03b1_400_, lean_object* v_x_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___f_403_; lean_object* v___x_404_; 
v___f_403_ = lean_alloc_closure((void*)(l_Std_Do_ReaderT_instWP___redArg___lam__1), 5, 3);
lean_closure_set(v___f_403_, 0, v_x_401_);
lean_closure_set(v___f_403_, 1, v_inst_398_);
lean_closure_set(v___f_403_, 2, v_ps_399_);
v___x_404_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushArg___redArg___lam__1), 3, 2);
lean_closure_set(v___x_404_, 0, v___f_403_);
lean_closure_set(v___x_404_, 1, v___y_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP___redArg(lean_object* v_ps_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___f_407_; 
v___f_407_ = lean_alloc_closure((void*)(l_Std_Do_ReaderT_instWP___redArg___lam__2), 5, 2);
lean_closure_set(v___f_407_, 0, v_inst_406_);
lean_closure_set(v___f_407_, 1, v_ps_405_);
return v___f_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWP(lean_object* v_m_408_, lean_object* v_ps_409_, lean_object* v_00_u03c1_410_, lean_object* v_inst_411_){
_start:
{
lean_object* v___f_412_; 
v___f_412_ = lean_alloc_closure((void*)(l_Std_Do_ReaderT_instWP___redArg___lam__2), 5, 2);
lean_closure_set(v___f_412_, 0, v_inst_411_);
lean_closure_set(v___f_412_, 1, v_ps_409_);
return v___f_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP___redArg___lam__0(lean_object* v_inst_413_, lean_object* v_00_u03b1_414_, lean_object* v_x_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_apply_2(v_inst_413_, lean_box(0), v_x_415_);
v___x_418_ = l_Std_Do_PredTrans_pushExcept___redArg___lam__1(v___x_417_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP___redArg(lean_object* v_inst_419_){
_start:
{
lean_object* v___f_420_; 
v___f_420_ = lean_alloc_closure((void*)(l_Std_Do_ExceptT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_420_, 0, v_inst_419_);
return v___f_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP(lean_object* v_m_421_, lean_object* v_ps_422_, lean_object* v_00_u03b5_423_, lean_object* v_inst_424_){
_start:
{
lean_object* v___f_425_; 
v___f_425_ = lean_alloc_closure((void*)(l_Std_Do_ExceptT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_425_, 0, v_inst_424_);
return v___f_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWP___boxed(lean_object* v_m_426_, lean_object* v_ps_427_, lean_object* v_00_u03b5_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_Do_ExceptT_instWP(v_m_426_, v_ps_427_, v_00_u03b5_428_, v_inst_429_);
lean_dec(v_ps_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP___redArg___lam__0(lean_object* v_inst_431_, lean_object* v_00_u03b1_432_, lean_object* v_x_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_apply_2(v_inst_431_, lean_box(0), v_x_433_);
v___x_436_ = l_Std_Do_PredTrans_pushOption___redArg___lam__1(v___x_435_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP___redArg(lean_object* v_inst_437_){
_start:
{
lean_object* v___f_438_; 
v___f_438_ = lean_alloc_closure((void*)(l_Std_Do_OptionT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_438_, 0, v_inst_437_);
return v___f_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP(lean_object* v_m_439_, lean_object* v_ps_440_, lean_object* v_inst_441_){
_start:
{
lean_object* v___f_442_; 
v___f_442_ = lean_alloc_closure((void*)(l_Std_Do_OptionT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_442_, 0, v_inst_441_);
return v___f_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWP___boxed(lean_object* v_m_443_, lean_object* v_ps_444_, lean_object* v_inst_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Do_OptionT_instWP(v_m_443_, v_ps_444_, v_inst_445_);
lean_dec(v_ps_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__0(lean_object* v___y_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_box(0);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__0___boxed(lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Do_EStateM_instWP___lam__0(v___y_449_);
lean_dec(v___y_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__1(lean_object* v___f_451_, lean_object* v_00_u03b1_452_, lean_object* v_x_453_, lean_object* v___y_454_){
_start:
{
lean_inc_ref(v___f_451_);
return v___f_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP___lam__1___boxed(lean_object* v___f_455_, lean_object* v_00_u03b1_456_, lean_object* v_x_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Do_EStateM_instWP___lam__1(v___f_455_, v_00_u03b1_456_, v_x_457_, v___y_458_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_x_457_);
lean_dec_ref(v___f_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWP(lean_object* v_00_u03b5_463_, lean_object* v_00_u03c3_464_){
_start:
{
lean_object* v___f_465_; 
v___f_465_ = ((lean_object*)(l_Std_Do_EStateM_instWP___closed__1));
return v___f_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_State_instWP___lam__0(lean_object* v_x_466_, lean_object* v_s_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_apply_1(v_x_466_, v_s_467_);
v___x_470_ = l_Std_Do_PredTrans_pure___redArg___lam__0(v___x_469_, v___y_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_State_instWP___lam__1(lean_object* v_00_u03b1_471_, lean_object* v_x_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___f_474_; lean_object* v___x_475_; 
v___f_474_ = lean_alloc_closure((void*)(l_Std_Do_State_instWP___lam__0), 3, 1);
lean_closure_set(v___f_474_, 0, v_x_472_);
v___x_475_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushArg___redArg___lam__1), 3, 2);
lean_closure_set(v___x_475_, 0, v___f_474_);
lean_closure_set(v___x_475_, 1, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_State_instWP(lean_object* v_00_u03c3_477_){
_start:
{
lean_object* v___f_478_; 
v___f_478_ = ((lean_object*)(l_Std_Do_State_instWP___closed__0));
return v___f_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWP___lam__1(lean_object* v_x_479_, lean_object* v___x_480_, lean_object* v_s_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_s_481_);
v___f_483_ = lean_alloc_closure((void*)(l_Std_Do_ReaderT_instWP___redArg___lam__0), 2, 1);
lean_closure_set(v___f_483_, 0, v_s_481_);
v___x_484_ = lean_apply_1(v_x_479_, v_s_481_);
v___f_485_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_485_, 0, v___x_484_);
v___x_486_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pure___boxed), 3, 2);
lean_closure_set(v___x_486_, 0, v___x_480_);
lean_closure_set(v___x_486_, 1, lean_box(0));
v___x_487_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_487_, 0, lean_box(0));
lean_closure_set(v___x_487_, 1, lean_box(0));
lean_closure_set(v___x_487_, 2, lean_box(0));
lean_closure_set(v___x_487_, 3, v___x_486_);
lean_closure_set(v___x_487_, 4, v___f_483_);
v___x_488_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_487_, v___f_485_, v___y_482_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWP___lam__0(lean_object* v___x_489_, lean_object* v_00_u03b1_490_, lean_object* v_x_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___f_493_; lean_object* v___x_494_; 
v___f_493_ = lean_alloc_closure((void*)(l_Std_Do_Reader_instWP___lam__1), 4, 2);
lean_closure_set(v___f_493_, 0, v_x_491_);
lean_closure_set(v___f_493_, 1, v___x_489_);
v___x_494_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushArg___redArg___lam__1), 3, 2);
lean_closure_set(v___x_494_, 0, v___f_493_);
lean_closure_set(v___x_494_, 1, v___y_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWP(lean_object* v_00_u03c1_497_){
_start:
{
lean_object* v___f_498_; 
v___f_498_ = ((lean_object*)(l_Std_Do_Reader_instWP___closed__0));
return v___f_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Except_instWP___aux__1___redArg(lean_object* v_x_499_){
_start:
{
lean_object* v___f_500_; lean_object* v___f_501_; 
v___f_500_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_500_, 0, v_x_499_);
v___f_501_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushExcept___redArg___lam__1), 2, 1);
lean_closure_set(v___f_501_, 0, v___f_500_);
return v___f_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Except_instWP___aux__1(lean_object* v_00_u03b5_502_, lean_object* v_00_u03b1_503_, lean_object* v_x_504_){
_start:
{
lean_object* v___f_505_; lean_object* v___f_506_; 
v___f_505_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_505_, 0, v_x_504_);
v___f_506_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushExcept___redArg___lam__1), 2, 1);
lean_closure_set(v___f_506_, 0, v___f_505_);
return v___f_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Except_instWP(lean_object* v_00_u03b5_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l_Std_Do_Except_instWP___closed__0));
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Option_instWP___aux__1___redArg(lean_object* v_x_510_){
_start:
{
lean_object* v___f_511_; lean_object* v___f_512_; 
v___f_511_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_511_, 0, v_x_510_);
v___f_512_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushOption___redArg___lam__1), 2, 1);
lean_closure_set(v___f_512_, 0, v___f_511_);
return v___f_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Option_instWP___aux__1(lean_object* v_00_u03b1_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___f_515_; lean_object* v___f_516_; 
v___f_515_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_515_, 0, v_x_514_);
v___f_516_ = lean_alloc_closure((void*)(l_Std_Do_PredTrans_pushOption___redArg___lam__1), 2, 1);
lean_closure_set(v___f_516_, 0, v___f_515_);
return v___f_516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* v_x_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
lean_dec(v_h__1_520_);
v_a_522_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v_x_519_);
v___x_523_ = lean_apply_1(v_h__2_521_, v_a_522_);
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_521_);
v_a_524_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v_x_519_);
v___x_525_ = lean_apply_1(v_h__1_520_, v_a_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b5_527_, lean_object* v_motive_528_, lean_object* v_x_529_, lean_object* v_h__1_530_, lean_object* v_h__2_531_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; 
lean_dec(v_h__1_530_);
v_a_532_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v_x_529_);
v___x_533_ = lean_apply_1(v_h__2_531_, v_a_532_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_535_; 
lean_dec(v_h__2_531_);
v_a_534_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_a_534_);
lean_dec_ref(v_x_529_);
v___x_535_ = lean_apply_1(v_h__1_530_, v_a_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_536_, lean_object* v_h__1_537_, lean_object* v_h__2_538_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v_h__1_537_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_apply_1(v_h__2_538_, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v_val_541_; lean_object* v___x_542_; 
lean_dec(v_h__2_538_);
v_val_541_ = lean_ctor_get(v_x_536_, 0);
lean_inc(v_val_541_);
lean_dec_ref(v_x_536_);
v___x_542_ = lean_apply_1(v_h__1_537_, v_val_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_543_, lean_object* v_motive_544_, lean_object* v_x_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_h__1_546_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_apply_1(v_h__2_547_, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v_val_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_547_);
v_val_550_ = lean_ctor_get(v_x_545_, 0);
lean_inc(v_val_550_);
lean_dec_ref(v_x_545_);
v___x_551_ = lean_apply_1(v_h__1_546_, v_val_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object* v_x_552_, lean_object* v_h__1_553_, lean_object* v_h__2_554_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v_a_555_; lean_object* v_a_556_; lean_object* v___x_557_; 
lean_dec(v_h__2_554_);
v_a_555_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_a_555_);
v_a_556_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_a_556_);
lean_dec_ref(v_x_552_);
v___x_557_ = lean_apply_2(v_h__1_553_, v_a_555_, v_a_556_);
return v___x_557_;
}
else
{
lean_object* v_a_558_; lean_object* v_a_559_; lean_object* v___x_560_; 
lean_dec(v_h__1_553_);
v_a_558_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_a_558_);
v_a_559_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_a_559_);
lean_dec_ref(v_x_552_);
v___x_560_ = lean_apply_2(v_h__2_554_, v_a_558_, v_a_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Basic_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object* v_00_u03b5_561_, lean_object* v_00_u03c3_562_, lean_object* v_00_u03b1_563_, lean_object* v_motive_564_, lean_object* v_x_565_, lean_object* v_h__1_566_, lean_object* v_h__2_567_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v_a_568_; lean_object* v_a_569_; lean_object* v___x_570_; 
lean_dec(v_h__2_567_);
v_a_568_ = lean_ctor_get(v_x_565_, 0);
lean_inc(v_a_568_);
v_a_569_ = lean_ctor_get(v_x_565_, 1);
lean_inc(v_a_569_);
lean_dec_ref(v_x_565_);
v___x_570_ = lean_apply_2(v_h__1_566_, v_a_568_, v_a_569_);
return v___x_570_;
}
else
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v___x_573_; 
lean_dec(v_h__1_566_);
v_a_571_ = lean_ctor_get(v_x_565_, 0);
lean_inc(v_a_571_);
v_a_572_ = lean_ctor_get(v_x_565_, 1);
lean_inc(v_a_572_);
lean_dec_ref(v_x_565_);
v___x_573_ = lean_apply_2(v_h__2_567_, v_a_571_, v_a_572_);
return v___x_573_;
}
}
}
lean_object* runtime_initialize_Std_Do_PredTrans(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_PredTrans(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_WP_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
