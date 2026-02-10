// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.RegisterCommand
// Imports: public import Lean.Meta.Tactic.Grind.Types public meta import Init.Data.ToString.Name
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
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__2_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__3_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__4 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__5 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "registerGrindAttr"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__6 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__6_value;
lean_object* l_Lean_Name_mkStr8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__7;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__8 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__9 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__9_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__10 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__11 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__11_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__12 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__13 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__13_value)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__14 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__11_value),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__14_value)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__15 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__15_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_grind_attr"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__16 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__16_value)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__17 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__9_value),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__15_value),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__18 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__18_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__19 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__19_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__20 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__20_value)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__21 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__9_value),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__18_value),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__21_value)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__22 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__22_value;
static lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__23;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_registerGrindAttr;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 140, 114, 135, 71, 133, 96, 5)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 12, 90, 240, 78, 252, 149, 89)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(65, 184, 222, 195, 211, 23, 22, 1)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(222, 145, 103, 225, 142, 169, 142, 153)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13_value),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "registerAttr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(98, 25, 4, 98, 170, 222, 222, 42)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(213, 19, 34, 154, 74, 108, 206, 181)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35_value;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(35, 123, 1, 146, 14, 217, 108, 179)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_\?"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(19, 110, 207, 78, 164, 149, 1, 207)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Parser.Attr.grindMod"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59_value;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62_value;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 207, 35, 177, 108, 73, 87)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Command_registerGrindAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__6));
x_2 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__5));
x_3 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__4));
x_4 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__3));
x_5 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__2));
x_6 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__1));
x_7 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__0));
x_8 = l_Lean_Name_mkStr8(x_7, x_6, x_5, x_4, x_7, x_3, x_2, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Command_registerGrindAttr___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__22));
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Command_registerGrindAttr___closed__7;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_registerGrindAttr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Command_registerGrindAttr___closed__23;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_166; uint8_t x_167; 
x_4 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__0));
x_5 = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__4));
x_166 = l_Lean_Parser_Command_registerGrindAttr___closed__7;
lean_inc(x_1);
x_167 = l_Lean_Syntax_isOfKind(x_1, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_168 = lean_box(1);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_3);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_210; 
x_170 = lean_unsigned_to_nat(0u);
x_171 = l_Lean_Syntax_getArg(x_1, x_170);
x_172 = lean_unsigned_to_nat(2u);
x_173 = l_Lean_Syntax_getArg(x_1, x_172);
lean_dec(x_1);
x_210 = l_Lean_Syntax_getOptional_x3f(x_171);
lean_dec(x_171);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_box(0);
x_174 = x_211;
goto block_209;
}
else
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_210);
if (x_212 == 0)
{
x_174 = x_210;
goto block_209;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_174 = x_214;
goto block_209;
}
}
block_209:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_175 = l_Lean_TSyntax_getId(x_173);
lean_inc(x_175);
x_176 = l_Lean_Name_toString(x_175, x_167);
x_177 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66));
x_178 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67));
lean_inc(x_175);
x_179 = l_Lean_Name_append(x_178, x_175);
x_180 = 0;
x_181 = l_Lean_mkIdentFrom(x_173, x_179, x_180);
x_182 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68));
lean_inc_ref(x_176);
x_183 = lean_string_append(x_176, x_182);
lean_inc(x_175);
x_184 = lean_name_append_after(x_175, x_182);
x_185 = l_Lean_Name_append(x_178, x_184);
x_186 = l_Lean_mkIdentFrom(x_173, x_185, x_180);
x_187 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69));
lean_inc_ref(x_176);
x_188 = lean_string_append(x_176, x_187);
x_189 = lean_ctor_get(x_2, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_2, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_2, 5);
lean_inc(x_191);
lean_dec_ref(x_2);
lean_inc(x_175);
x_192 = lean_name_append_after(x_175, x_187);
x_193 = l_Lean_Name_append(x_178, x_192);
x_194 = l_Lean_mkIdentFrom(x_173, x_193, x_180);
x_195 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70));
lean_inc_ref(x_176);
x_196 = lean_string_append(x_176, x_195);
lean_inc(x_175);
x_197 = lean_name_append_after(x_175, x_195);
x_198 = l_Lean_Name_append(x_178, x_197);
x_199 = l_Lean_mkIdentFrom(x_173, x_198, x_180);
lean_dec(x_173);
x_200 = l_Lean_SourceInfo_fromRef(x_191, x_180);
lean_dec(x_191);
x_201 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72));
x_202 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73));
x_203 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74));
x_204 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76));
x_205 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77;
if (lean_obj_tag(x_174) == 1)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_174, 0);
lean_inc(x_206);
lean_dec_ref(x_174);
x_207 = l_Array_mkArray1___redArg(x_206);
x_6 = x_183;
x_7 = x_203;
x_8 = x_196;
x_9 = x_200;
x_10 = x_186;
x_11 = x_199;
x_12 = x_194;
x_13 = x_177;
x_14 = x_205;
x_15 = x_189;
x_16 = x_201;
x_17 = x_190;
x_18 = x_204;
x_19 = x_188;
x_20 = x_202;
x_21 = x_187;
x_22 = x_175;
x_23 = x_181;
x_24 = x_176;
x_25 = x_207;
goto block_165;
}
else
{
lean_object* x_208; 
lean_dec(x_174);
x_208 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78;
x_6 = x_183;
x_7 = x_203;
x_8 = x_196;
x_9 = x_200;
x_10 = x_186;
x_11 = x_199;
x_12 = x_194;
x_13 = x_177;
x_14 = x_205;
x_15 = x_189;
x_16 = x_201;
x_17 = x_190;
x_18 = x_204;
x_19 = x_188;
x_20 = x_202;
x_21 = x_187;
x_22 = x_175;
x_23 = x_181;
x_24 = x_176;
x_25 = x_208;
goto block_165;
}
}
}
block_165:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_inc_ref(x_14);
x_26 = l_Array_append___redArg(x_14, x_25);
lean_dec_ref(x_25);
lean_inc(x_16);
lean_inc(x_9);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_16);
lean_inc(x_9);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_16);
lean_ctor_set(x_28, 2, x_14);
lean_inc_ref_n(x_28, 6);
lean_inc_ref(x_27);
lean_inc(x_9);
x_29 = l_Lean_Syntax_node7(x_9, x_18, x_27, x_28, x_28, x_28, x_28, x_28, x_28);
x_30 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1));
lean_inc(x_9);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_20);
lean_inc(x_9);
x_32 = l_Lean_Syntax_node1(x_9, x_30, x_31);
x_33 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3;
x_34 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4));
lean_inc(x_17);
lean_inc(x_15);
x_35 = l_Lean_addMacroScope(x_15, x_34, x_17);
x_36 = lean_box(0);
lean_inc(x_9);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7));
x_39 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8));
lean_inc(x_9);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10;
x_42 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11));
lean_inc(x_17);
lean_inc(x_15);
x_43 = l_Lean_addMacroScope(x_15, x_42, x_17);
x_44 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16));
lean_inc(x_9);
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_44);
lean_inc_ref(x_40);
lean_inc(x_9);
x_46 = l_Lean_Syntax_node2(x_9, x_38, x_40, x_45);
x_47 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17));
lean_inc(x_9);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_16);
lean_inc(x_9);
x_49 = l_Lean_Syntax_node3(x_9, x_16, x_37, x_46, x_48);
x_50 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19));
x_51 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21));
x_52 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23));
x_53 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25));
x_54 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27;
x_55 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28));
lean_inc(x_17);
lean_inc(x_15);
x_56 = l_Lean_addMacroScope(x_15, x_55, x_17);
x_57 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31));
lean_inc(x_9);
x_58 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_58, 0, x_9);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
x_59 = l_Lean_instQuoteNameMkStr1___private__1(x_22);
x_60 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33));
x_61 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34));
lean_inc(x_9);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_9);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36;
x_64 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37));
lean_inc(x_17);
lean_inc(x_15);
x_65 = l_Lean_addMacroScope(x_15, x_64, x_17);
lean_inc(x_9);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_36);
x_67 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38));
lean_inc(x_9);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_9);
lean_ctor_set(x_68, 1, x_67);
x_69 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39));
lean_inc(x_9);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_69);
lean_inc_ref(x_70);
lean_inc(x_59);
lean_inc_ref(x_68);
lean_inc_ref(x_62);
lean_inc(x_9);
x_71 = l_Lean_Syntax_node5(x_9, x_60, x_62, x_66, x_68, x_59, x_70);
lean_inc(x_16);
lean_inc(x_9);
x_72 = l_Lean_Syntax_node2(x_9, x_16, x_59, x_71);
lean_inc(x_9);
x_73 = l_Lean_Syntax_node2(x_9, x_53, x_58, x_72);
lean_inc(x_9);
x_74 = l_Lean_Syntax_node1(x_9, x_52, x_73);
lean_inc_ref(x_28);
lean_inc(x_9);
x_75 = l_Lean_Syntax_node2(x_9, x_51, x_74, x_28);
lean_inc(x_16);
lean_inc(x_9);
x_76 = l_Lean_Syntax_node1(x_9, x_16, x_75);
lean_inc(x_9);
x_77 = l_Lean_Syntax_node1(x_9, x_50, x_76);
lean_inc(x_9);
x_78 = l_Lean_Syntax_node4(x_9, x_7, x_29, x_32, x_49, x_77);
x_79 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40));
x_80 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41));
x_81 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43));
lean_inc_ref(x_28);
lean_inc(x_9);
x_82 = l_Lean_Syntax_node1(x_9, x_81, x_28);
lean_inc(x_9);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_9);
lean_ctor_set(x_83, 1, x_79);
x_84 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45));
x_85 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46));
lean_inc(x_9);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_9);
lean_ctor_set(x_86, 1, x_85);
lean_inc_ref(x_70);
lean_inc_ref(x_68);
lean_inc_ref(x_86);
lean_inc_ref(x_62);
lean_inc(x_9);
x_87 = l_Lean_Syntax_node5(x_9, x_84, x_62, x_86, x_68, x_23, x_70);
lean_inc(x_16);
lean_inc(x_9);
x_88 = l_Lean_Syntax_node1(x_9, x_16, x_87);
x_89 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49));
x_90 = lean_box(2);
x_91 = l_Lean_Syntax_mkStrLit(x_24, x_90);
lean_inc(x_9);
x_92 = l_Lean_Syntax_node1(x_9, x_89, x_91);
x_93 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51));
x_94 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53));
x_95 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55));
x_96 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57;
x_97 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58));
lean_inc(x_17);
lean_inc(x_15);
x_98 = l_Lean_addMacroScope(x_15, x_97, x_17);
lean_inc(x_9);
x_99 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_99, 0, x_9);
lean_ctor_set(x_99, 1, x_96);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_36);
lean_inc_ref(x_28);
lean_inc(x_9);
x_100 = l_Lean_Syntax_node2(x_9, x_95, x_99, x_28);
x_101 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60;
x_102 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61));
x_103 = l_Lean_Name_mkStr4(x_4, x_5, x_13, x_102);
lean_inc(x_17);
lean_inc(x_103);
lean_inc(x_15);
x_104 = l_Lean_addMacroScope(x_15, x_103, x_17);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_36);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_36);
lean_inc(x_9);
x_107 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_107, 0, x_9);
lean_ctor_set(x_107, 1, x_101);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_106);
lean_inc_ref(x_28);
lean_inc(x_9);
x_108 = l_Lean_Syntax_node2(x_9, x_95, x_107, x_28);
lean_inc(x_16);
lean_inc(x_9);
x_109 = l_Lean_Syntax_node2(x_9, x_16, x_100, x_108);
lean_inc_ref(x_70);
lean_inc_ref(x_62);
lean_inc(x_9);
x_110 = l_Lean_Syntax_node3(x_9, x_94, x_62, x_109, x_70);
lean_inc(x_9);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_9);
lean_ctor_set(x_111, 1, x_21);
lean_inc(x_9);
x_112 = l_Lean_Syntax_node2(x_9, x_93, x_110, x_111);
lean_inc(x_112);
lean_inc(x_16);
lean_inc(x_9);
x_113 = l_Lean_Syntax_node2(x_9, x_16, x_92, x_112);
x_114 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63;
x_115 = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64));
x_116 = l_Lean_addMacroScope(x_15, x_115, x_17);
lean_inc(x_9);
x_117 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_117, 0, x_9);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_36);
x_118 = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65;
x_119 = lean_array_push(x_118, x_27);
lean_inc_ref(x_28);
x_120 = lean_array_push(x_119, x_28);
x_121 = lean_array_push(x_120, x_82);
x_122 = lean_array_push(x_121, x_83);
lean_inc_ref(x_28);
x_123 = lean_array_push(x_122, x_28);
lean_inc_ref(x_123);
x_124 = lean_array_push(x_123, x_88);
lean_inc_ref(x_28);
x_125 = lean_array_push(x_124, x_28);
x_126 = lean_array_push(x_125, x_113);
lean_inc_ref(x_40);
x_127 = lean_array_push(x_126, x_40);
lean_inc_ref(x_117);
x_128 = lean_array_push(x_127, x_117);
lean_inc(x_9);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_9);
lean_ctor_set(x_129, 1, x_80);
lean_ctor_set(x_129, 2, x_128);
lean_inc_ref(x_70);
lean_inc_ref(x_68);
lean_inc_ref(x_86);
lean_inc_ref(x_62);
lean_inc(x_9);
x_130 = l_Lean_Syntax_node5(x_9, x_84, x_62, x_86, x_68, x_10, x_70);
lean_inc(x_16);
lean_inc(x_9);
x_131 = l_Lean_Syntax_node1(x_9, x_16, x_130);
x_132 = l_Lean_Syntax_mkStrLit(x_6, x_90);
lean_inc(x_9);
x_133 = l_Lean_Syntax_node1(x_9, x_89, x_132);
lean_inc(x_112);
lean_inc(x_16);
lean_inc(x_9);
x_134 = l_Lean_Syntax_node2(x_9, x_16, x_133, x_112);
lean_inc_ref(x_123);
x_135 = lean_array_push(x_123, x_131);
lean_inc_ref(x_28);
x_136 = lean_array_push(x_135, x_28);
x_137 = lean_array_push(x_136, x_134);
lean_inc_ref(x_40);
x_138 = lean_array_push(x_137, x_40);
lean_inc_ref(x_117);
x_139 = lean_array_push(x_138, x_117);
lean_inc(x_9);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_9);
lean_ctor_set(x_140, 1, x_80);
lean_ctor_set(x_140, 2, x_139);
lean_inc_ref(x_70);
lean_inc_ref(x_68);
lean_inc_ref(x_86);
lean_inc_ref(x_62);
lean_inc(x_9);
x_141 = l_Lean_Syntax_node5(x_9, x_84, x_62, x_86, x_68, x_12, x_70);
lean_inc(x_16);
lean_inc(x_9);
x_142 = l_Lean_Syntax_node1(x_9, x_16, x_141);
x_143 = l_Lean_Syntax_mkStrLit(x_19, x_90);
lean_inc(x_9);
x_144 = l_Lean_Syntax_node1(x_9, x_89, x_143);
lean_inc(x_112);
lean_inc(x_16);
lean_inc(x_9);
x_145 = l_Lean_Syntax_node2(x_9, x_16, x_144, x_112);
lean_inc_ref(x_123);
x_146 = lean_array_push(x_123, x_142);
lean_inc_ref(x_28);
x_147 = lean_array_push(x_146, x_28);
x_148 = lean_array_push(x_147, x_145);
lean_inc_ref(x_40);
x_149 = lean_array_push(x_148, x_40);
lean_inc_ref(x_117);
x_150 = lean_array_push(x_149, x_117);
lean_inc(x_9);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_9);
lean_ctor_set(x_151, 1, x_80);
lean_ctor_set(x_151, 2, x_150);
lean_inc(x_9);
x_152 = l_Lean_Syntax_node5(x_9, x_84, x_62, x_86, x_68, x_11, x_70);
lean_inc(x_16);
lean_inc(x_9);
x_153 = l_Lean_Syntax_node1(x_9, x_16, x_152);
x_154 = l_Lean_Syntax_mkStrLit(x_8, x_90);
lean_inc(x_9);
x_155 = l_Lean_Syntax_node1(x_9, x_89, x_154);
lean_inc(x_16);
lean_inc(x_9);
x_156 = l_Lean_Syntax_node2(x_9, x_16, x_155, x_112);
x_157 = lean_array_push(x_123, x_153);
x_158 = lean_array_push(x_157, x_28);
x_159 = lean_array_push(x_158, x_156);
x_160 = lean_array_push(x_159, x_40);
x_161 = lean_array_push(x_160, x_117);
lean_inc(x_9);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_9);
lean_ctor_set(x_162, 1, x_80);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_Syntax_node5(x_9, x_16, x_78, x_129, x_140, x_151, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_3);
return x_164;
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Command_registerGrindAttr___closed__7 = _init_l_Lean_Parser_Command_registerGrindAttr___closed__7();
lean_mark_persistent(l_Lean_Parser_Command_registerGrindAttr___closed__7);
l_Lean_Parser_Command_registerGrindAttr___closed__23 = _init_l_Lean_Parser_Command_registerGrindAttr___closed__23();
lean_mark_persistent(l_Lean_Parser_Command_registerGrindAttr___closed__23);
l_Lean_Parser_Command_registerGrindAttr = _init_l_Lean_Parser_Command_registerGrindAttr();
lean_mark_persistent(l_Lean_Parser_Command_registerGrindAttr);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77);
l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78 = _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78();
lean_mark_persistent(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
