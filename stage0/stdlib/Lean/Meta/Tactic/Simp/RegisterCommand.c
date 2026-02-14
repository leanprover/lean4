// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.RegisterCommand
// Imports: public import Lean.Meta.Tactic.Simp.Attr public meta import Lean.Meta.Tactic.Simp.Simproc
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
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__2_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__3_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__4 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__5 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "registerSimpAttr"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__6 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__6_value;
lean_object* l_Lean_Name_mkStr8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__7;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__8 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__9 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__9_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__10 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__11 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__11_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__12 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__13 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__13_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__14 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__11_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__14_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__15 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__15_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "register_simp_attr"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__16 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__16_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__17 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__9_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__15_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__18 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__18_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__19 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__19_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__20 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__20_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__21 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__9_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__18_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__21_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__22 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__22_value;
static lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__23;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_registerSimpAttr;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 247, 59, 43, 44, 177, 111, 66)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(113, 140, 114, 135, 71, 133, 96, 5)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(241, 12, 90, 240, 78, 252, 149, 89)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SimpExtension"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(97, 27, 52, 253, 143, 150, 102, 25)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(180, 63, 186, 197, 159, 200, 30, 167)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(71, 112, 199, 159, 165, 140, 183, 115)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(122, 223, 126, 22, 173, 44, 201, 149)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_\?"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(19, 110, 207, 78, 164, 149, 1, 207)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stx_<|>_"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(198, 97, 122, 56, 37, 186, 212, 102)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Parser.Tactic.simpPre"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(211, 17, 253, 157, 167, 104, 244, 4)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(84, 84, 229, 98, 67, 120, 70, 231)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<|>"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Parser.Tactic.simpPost"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(211, 17, 253, 157, 167, 104, 244, 4)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(151, 85, 122, 79, 145, 83, 124, 126)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unary"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(48, 77, 42, 108, 13, 102, 39, 65)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternIgnore"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(195, 83, 213, 191, 208, 4, 123, 240)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = "\"← \""};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\"<- \""};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82_value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 207, 35, 177, 108, 73, 87)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value_aux_2),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/--"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Simplification procedure -/"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extProc"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value),LEAN_SCALAR_PTR_LITERAL(153, 229, 121, 159, 4, 151, 74, 120)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SimprocExtension"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value),LEAN_SCALAR_PTR_LITERAL(48, 218, 30, 199, 10, 134, 135, 45)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value),LEAN_SCALAR_PTR_LITERAL(65, 33, 38, 245, 236, 63, 101, 240)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101_value)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "registerSimprocAttr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value),LEAN_SCALAR_PTR_LITERAL(153, 150, 186, 46, 228, 1, 156, 51)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value),LEAN_SCALAR_PTR_LITERAL(216, 40, 141, 126, 136, 240, 55, 143)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simproc set for "};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__118 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__118_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__119 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__119_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__121 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__121_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__121_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__123;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__124;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__125 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__125_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__126_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__126_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__125_value),LEAN_SCALAR_PTR_LITERAL(10, 9, 185, 250, 127, 107, 245, 225)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__126 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__126_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simp set for "};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__127 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__127_value;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Command_registerSimpAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__6));
x_2 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__5));
x_3 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__4));
x_4 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__3));
x_5 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__2));
x_6 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__1));
x_7 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__0));
x_8 = l_Lean_Name_mkStr8(x_7, x_6, x_5, x_4, x_7, x_3, x_2, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Command_registerSimpAttr___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__22));
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Command_registerSimpAttr___closed__7;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_registerSimpAttr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Command_registerSimpAttr___closed__23;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__6));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__123() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__124() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_215; uint8_t x_216; 
x_215 = l_Lean_Parser_Command_registerSimpAttr___closed__7;
lean_inc(x_1);
x_216 = l_Lean_Syntax_isOfKind(x_1, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_217 = lean_box(1);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_3);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_255; lean_object* x_267; 
x_219 = lean_unsigned_to_nat(0u);
x_220 = l_Lean_Syntax_getArg(x_1, x_219);
x_221 = lean_unsigned_to_nat(2u);
x_222 = l_Lean_Syntax_getArg(x_1, x_221);
lean_dec(x_1);
x_267 = l_Lean_Syntax_getOptional_x3f(x_220);
lean_dec(x_220);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
x_268 = lean_box(0);
x_255 = x_268;
goto block_266;
}
else
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_267);
if (x_269 == 0)
{
x_255 = x_267;
goto block_266;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_267, 0);
lean_inc(x_270);
lean_dec(x_267);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_255 = x_271;
goto block_266;
}
}
block_254:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_230 = lean_ctor_get(x_2, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_2, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_2, 5);
lean_inc(x_232);
lean_dec_ref(x_2);
x_233 = l_String_removeLeadingSpaces(x_229);
x_234 = lean_box(2);
x_235 = l_Lean_Syntax_mkStrLit(x_233, x_234);
lean_inc(x_226);
x_236 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_226);
x_237 = l_Lean_mkIdentFrom(x_222, x_236, x_224);
lean_dec(x_222);
x_238 = l_Lean_TSyntax_getId(x_237);
lean_inc(x_238);
x_239 = l_Lean_Name_toString(x_238, x_216);
lean_inc(x_238);
x_240 = l_Lean_Name_append(x_225, x_238);
x_241 = l_Lean_mkIdentFrom(x_237, x_240, x_224);
lean_dec(x_237);
x_242 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116));
x_243 = lean_string_append(x_242, x_239);
x_244 = l_Lean_Syntax_mkStrLit(x_243, x_234);
x_245 = l_Lean_SourceInfo_fromRef(x_232, x_224);
lean_dec(x_232);
x_246 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__118));
x_247 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__119));
x_248 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__120));
x_249 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__122));
x_250 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__123;
if (lean_obj_tag(x_223) == 1)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_223, 0);
lean_inc(x_251);
lean_dec_ref(x_223);
x_252 = l_Array_mkArray1___redArg(x_251);
x_4 = x_238;
x_5 = x_245;
x_6 = x_250;
x_7 = x_241;
x_8 = x_235;
x_9 = x_246;
x_10 = x_230;
x_11 = x_247;
x_12 = x_248;
x_13 = x_249;
x_14 = x_231;
x_15 = x_239;
x_16 = x_226;
x_17 = x_228;
x_18 = x_227;
x_19 = x_244;
x_20 = x_234;
x_21 = x_252;
goto block_214;
}
else
{
lean_object* x_253; 
lean_dec(x_223);
x_253 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__124;
x_4 = x_238;
x_5 = x_245;
x_6 = x_250;
x_7 = x_241;
x_8 = x_235;
x_9 = x_246;
x_10 = x_230;
x_11 = x_247;
x_12 = x_248;
x_13 = x_249;
x_14 = x_231;
x_15 = x_239;
x_16 = x_226;
x_17 = x_228;
x_18 = x_227;
x_19 = x_244;
x_20 = x_234;
x_21 = x_253;
goto block_214;
}
}
block_266:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; 
x_256 = l_Lean_TSyntax_getId(x_222);
lean_inc(x_256);
x_257 = l_Lean_Name_toString(x_256, x_216);
x_258 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__126));
lean_inc(x_256);
x_259 = l_Lean_Name_append(x_258, x_256);
x_260 = 0;
x_261 = l_Lean_mkIdentFrom(x_222, x_259, x_260);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__127));
x_263 = lean_string_append(x_262, x_257);
x_223 = x_255;
x_224 = x_260;
x_225 = x_258;
x_226 = x_256;
x_227 = x_257;
x_228 = x_261;
x_229 = x_263;
goto block_254;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_255, 0);
x_265 = l_Lean_TSyntax_getDocString(x_264);
x_223 = x_255;
x_224 = x_260;
x_225 = x_258;
x_226 = x_256;
x_227 = x_257;
x_228 = x_261;
x_229 = x_265;
goto block_254;
}
}
}
block_214:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_inc_ref(x_6);
x_22 = l_Array_append___redArg(x_6, x_21);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc(x_5);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_9);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_9);
lean_inc(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_6);
x_25 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0));
x_26 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1));
lean_inc(x_5);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
lean_inc(x_5);
x_28 = l_Lean_Syntax_node1(x_5, x_26, x_27);
lean_inc(x_9);
lean_inc(x_5);
x_29 = l_Lean_Syntax_node1(x_5, x_9, x_28);
x_30 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2));
x_31 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3));
lean_inc(x_5);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_30);
lean_inc(x_5);
x_33 = l_Lean_Syntax_node1(x_5, x_31, x_32);
lean_inc(x_9);
lean_inc(x_5);
x_34 = l_Lean_Syntax_node1(x_5, x_9, x_33);
lean_inc(x_34);
lean_inc(x_29);
lean_inc_ref_n(x_24, 4);
lean_inc_ref(x_23);
lean_inc(x_13);
lean_inc(x_5);
x_35 = l_Lean_Syntax_node7(x_5, x_13, x_23, x_24, x_29, x_24, x_34, x_24, x_24);
x_36 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5));
lean_inc(x_5);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_11);
lean_inc(x_5);
x_38 = l_Lean_Syntax_node1(x_5, x_36, x_37);
x_39 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7;
x_40 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8));
lean_inc(x_14);
lean_inc(x_10);
x_41 = l_Lean_addMacroScope(x_10, x_40, x_14);
x_42 = lean_box(0);
lean_inc(x_5);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
x_44 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11));
x_45 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12));
lean_inc(x_5);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14;
x_48 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15));
lean_inc(x_14);
lean_inc(x_10);
x_49 = l_Lean_addMacroScope(x_10, x_48, x_14);
x_50 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20));
lean_inc(x_5);
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_50);
lean_inc_ref(x_46);
lean_inc(x_5);
x_52 = l_Lean_Syntax_node2(x_5, x_44, x_46, x_51);
x_53 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21));
lean_inc(x_5);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_5);
lean_ctor_set(x_54, 1, x_53);
lean_inc_ref(x_54);
lean_inc(x_9);
lean_inc(x_5);
x_55 = l_Lean_Syntax_node3(x_5, x_9, x_43, x_52, x_54);
x_56 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23));
x_57 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25));
x_58 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27));
x_59 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29));
x_60 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30;
x_61 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31));
lean_inc(x_14);
lean_inc(x_10);
x_62 = l_Lean_addMacroScope(x_10, x_61, x_14);
x_63 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34));
lean_inc(x_5);
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_63);
x_65 = l_Lean_instQuoteNameMkStr1___private__1(x_16);
lean_inc(x_9);
lean_inc(x_5);
x_66 = l_Lean_Syntax_node2(x_5, x_9, x_65, x_8);
lean_inc(x_5);
x_67 = l_Lean_Syntax_node2(x_5, x_59, x_64, x_66);
lean_inc(x_5);
x_68 = l_Lean_Syntax_node1(x_5, x_58, x_67);
lean_inc_ref(x_24);
lean_inc(x_5);
x_69 = l_Lean_Syntax_node2(x_5, x_57, x_68, x_24);
lean_inc(x_9);
lean_inc(x_5);
x_70 = l_Lean_Syntax_node1(x_5, x_9, x_69);
lean_inc(x_5);
x_71 = l_Lean_Syntax_node1(x_5, x_56, x_70);
lean_inc(x_38);
lean_inc(x_12);
lean_inc(x_5);
x_72 = l_Lean_Syntax_node4(x_5, x_12, x_35, x_38, x_55, x_71);
x_73 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35));
x_74 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36));
x_75 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38));
lean_inc_ref(x_24);
lean_inc(x_5);
x_76 = l_Lean_Syntax_node1(x_5, x_75, x_24);
lean_inc(x_5);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_73);
x_78 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40));
x_79 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41));
lean_inc(x_5);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_79);
x_81 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42));
lean_inc(x_5);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_5);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43));
lean_inc(x_5);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_5);
lean_ctor_set(x_84, 1, x_83);
x_85 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44));
lean_inc(x_5);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_5);
lean_ctor_set(x_86, 1, x_85);
lean_inc_ref(x_86);
lean_inc_ref(x_84);
lean_inc_ref(x_82);
lean_inc_ref(x_80);
lean_inc(x_5);
x_87 = l_Lean_Syntax_node5(x_5, x_78, x_80, x_82, x_84, x_17, x_86);
lean_inc(x_9);
lean_inc(x_5);
x_88 = l_Lean_Syntax_node1(x_5, x_9, x_87);
x_89 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47));
lean_inc(x_20);
x_90 = l_Lean_Syntax_mkStrLit(x_18, x_20);
lean_inc(x_5);
x_91 = l_Lean_Syntax_node1(x_5, x_89, x_90);
x_92 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49));
x_93 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51));
x_94 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53));
x_95 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55));
x_96 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57;
x_97 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60));
lean_inc(x_14);
lean_inc(x_10);
x_98 = l_Lean_addMacroScope(x_10, x_97, x_14);
x_99 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63));
lean_inc(x_5);
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_5);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_98);
lean_ctor_set(x_100, 3, x_99);
lean_inc_ref(x_24);
lean_inc(x_5);
x_101 = l_Lean_Syntax_node2(x_5, x_95, x_100, x_24);
x_102 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64));
lean_inc(x_5);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_5);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66;
x_105 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68));
lean_inc(x_14);
lean_inc(x_10);
x_106 = l_Lean_addMacroScope(x_10, x_105, x_14);
x_107 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71));
lean_inc(x_5);
x_108 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_108, 0, x_5);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_106);
lean_ctor_set(x_108, 3, x_107);
lean_inc_ref(x_24);
lean_inc(x_5);
x_109 = l_Lean_Syntax_node2(x_5, x_95, x_108, x_24);
lean_inc_ref(x_103);
lean_inc(x_5);
x_110 = l_Lean_Syntax_node3(x_5, x_94, x_101, x_103, x_109);
lean_inc(x_9);
lean_inc(x_5);
x_111 = l_Lean_Syntax_node1(x_5, x_9, x_110);
lean_inc_ref(x_86);
lean_inc_ref(x_80);
lean_inc(x_5);
x_112 = l_Lean_Syntax_node3(x_5, x_93, x_80, x_111, x_86);
x_113 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72));
lean_inc(x_5);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_5);
lean_ctor_set(x_114, 1, x_113);
lean_inc_ref(x_114);
lean_inc(x_5);
x_115 = l_Lean_Syntax_node2(x_5, x_92, x_112, x_114);
x_116 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74));
x_117 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76;
x_118 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77));
lean_inc(x_14);
lean_inc(x_10);
x_119 = l_Lean_addMacroScope(x_10, x_118, x_14);
lean_inc(x_5);
x_120 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_120, 0, x_5);
lean_ctor_set(x_120, 1, x_117);
lean_ctor_set(x_120, 2, x_119);
lean_ctor_set(x_120, 3, x_42);
x_121 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79));
x_122 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80));
lean_inc(x_5);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_5);
lean_ctor_set(x_123, 1, x_122);
lean_inc(x_5);
x_124 = l_Lean_Syntax_node1(x_5, x_121, x_123);
lean_inc(x_5);
x_125 = l_Lean_Syntax_node1(x_5, x_89, x_124);
x_126 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81));
lean_inc(x_5);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_5);
lean_ctor_set(x_127, 1, x_126);
lean_inc(x_5);
x_128 = l_Lean_Syntax_node1(x_5, x_121, x_127);
lean_inc(x_5);
x_129 = l_Lean_Syntax_node1(x_5, x_89, x_128);
lean_inc(x_5);
x_130 = l_Lean_Syntax_node3(x_5, x_94, x_125, x_103, x_129);
lean_inc(x_9);
lean_inc(x_5);
x_131 = l_Lean_Syntax_node1(x_5, x_9, x_130);
lean_inc_ref(x_86);
lean_inc_ref(x_80);
lean_inc(x_5);
x_132 = l_Lean_Syntax_node4(x_5, x_116, x_120, x_80, x_131, x_86);
lean_inc_ref(x_114);
lean_inc(x_5);
x_133 = l_Lean_Syntax_node2(x_5, x_92, x_132, x_114);
x_134 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83;
x_135 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84));
lean_inc(x_14);
lean_inc(x_10);
x_136 = l_Lean_addMacroScope(x_10, x_135, x_14);
lean_inc(x_5);
x_137 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_137, 0, x_5);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_42);
lean_inc_ref(x_24);
lean_inc(x_5);
x_138 = l_Lean_Syntax_node2(x_5, x_95, x_137, x_24);
lean_inc(x_9);
lean_inc(x_5);
x_139 = l_Lean_Syntax_node1(x_5, x_9, x_138);
lean_inc_ref(x_86);
lean_inc_ref(x_80);
lean_inc(x_5);
x_140 = l_Lean_Syntax_node3(x_5, x_93, x_80, x_139, x_86);
lean_inc(x_5);
x_141 = l_Lean_Syntax_node2(x_5, x_92, x_140, x_114);
lean_inc(x_115);
lean_inc(x_9);
lean_inc(x_5);
x_142 = l_Lean_Syntax_node4(x_5, x_9, x_91, x_115, x_133, x_141);
x_143 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86;
x_144 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87));
lean_inc(x_14);
lean_inc(x_10);
x_145 = l_Lean_addMacroScope(x_10, x_144, x_14);
lean_inc(x_5);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_5);
lean_ctor_set(x_146, 1, x_143);
lean_ctor_set(x_146, 2, x_145);
lean_ctor_set(x_146, 3, x_42);
x_147 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88;
x_148 = lean_array_push(x_147, x_23);
lean_inc_ref(x_24);
x_149 = lean_array_push(x_148, x_24);
lean_inc(x_76);
x_150 = lean_array_push(x_149, x_76);
lean_inc_ref(x_77);
x_151 = lean_array_push(x_150, x_77);
lean_inc_ref(x_24);
x_152 = lean_array_push(x_151, x_24);
x_153 = lean_array_push(x_152, x_88);
lean_inc_ref(x_24);
x_154 = lean_array_push(x_153, x_24);
x_155 = lean_array_push(x_154, x_142);
lean_inc_ref(x_46);
x_156 = lean_array_push(x_155, x_46);
lean_inc_ref(x_146);
x_157 = lean_array_push(x_156, x_146);
lean_inc(x_5);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_5);
lean_ctor_set(x_158, 1, x_74);
lean_ctor_set(x_158, 2, x_157);
x_159 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89));
x_160 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90));
lean_inc(x_5);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_5);
lean_ctor_set(x_161, 1, x_160);
x_162 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91));
lean_inc(x_5);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_5);
lean_ctor_set(x_163, 1, x_162);
lean_inc(x_5);
x_164 = l_Lean_Syntax_node2(x_5, x_159, x_161, x_163);
lean_inc(x_9);
lean_inc(x_5);
x_165 = l_Lean_Syntax_node1(x_5, x_9, x_164);
lean_inc_ref_n(x_24, 4);
lean_inc(x_165);
lean_inc(x_5);
x_166 = l_Lean_Syntax_node7(x_5, x_13, x_165, x_24, x_29, x_24, x_34, x_24, x_24);
x_167 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93;
x_168 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94));
lean_inc(x_14);
lean_inc(x_10);
x_169 = l_Lean_addMacroScope(x_10, x_168, x_14);
lean_inc(x_5);
x_170 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_170, 0, x_5);
lean_ctor_set(x_170, 1, x_167);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_42);
x_171 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96;
x_172 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97));
lean_inc(x_14);
lean_inc(x_10);
x_173 = l_Lean_addMacroScope(x_10, x_172, x_14);
x_174 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102));
lean_inc(x_5);
x_175 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_175, 0, x_5);
lean_ctor_set(x_175, 1, x_171);
lean_ctor_set(x_175, 2, x_173);
lean_ctor_set(x_175, 3, x_174);
lean_inc_ref(x_46);
lean_inc(x_5);
x_176 = l_Lean_Syntax_node2(x_5, x_44, x_46, x_175);
lean_inc(x_9);
lean_inc(x_5);
x_177 = l_Lean_Syntax_node3(x_5, x_9, x_170, x_176, x_54);
x_178 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104;
x_179 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105));
lean_inc(x_14);
lean_inc(x_10);
x_180 = l_Lean_addMacroScope(x_10, x_179, x_14);
x_181 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108));
lean_inc(x_5);
x_182 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_182, 0, x_5);
lean_ctor_set(x_182, 1, x_178);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
x_183 = l_Lean_instQuoteNameMkStr1___private__1(x_4);
x_184 = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110;
x_185 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111));
x_186 = l_Lean_addMacroScope(x_10, x_185, x_14);
x_187 = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115));
lean_inc(x_5);
x_188 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_188, 0, x_5);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_inc(x_9);
lean_inc(x_5);
x_189 = l_Lean_Syntax_node3(x_5, x_9, x_183, x_19, x_188);
lean_inc(x_5);
x_190 = l_Lean_Syntax_node2(x_5, x_59, x_182, x_189);
lean_inc(x_5);
x_191 = l_Lean_Syntax_node1(x_5, x_58, x_190);
lean_inc_ref(x_24);
lean_inc(x_5);
x_192 = l_Lean_Syntax_node2(x_5, x_57, x_191, x_24);
lean_inc(x_9);
lean_inc(x_5);
x_193 = l_Lean_Syntax_node1(x_5, x_9, x_192);
lean_inc(x_5);
x_194 = l_Lean_Syntax_node1(x_5, x_56, x_193);
lean_inc(x_5);
x_195 = l_Lean_Syntax_node4(x_5, x_12, x_166, x_38, x_177, x_194);
lean_inc(x_5);
x_196 = l_Lean_Syntax_node5(x_5, x_78, x_80, x_82, x_84, x_7, x_86);
lean_inc(x_9);
lean_inc(x_5);
x_197 = l_Lean_Syntax_node1(x_5, x_9, x_196);
x_198 = l_Lean_Syntax_mkStrLit(x_15, x_20);
lean_inc(x_5);
x_199 = l_Lean_Syntax_node1(x_5, x_89, x_198);
lean_inc(x_9);
lean_inc(x_5);
x_200 = l_Lean_Syntax_node2(x_5, x_9, x_199, x_115);
x_201 = lean_array_push(x_147, x_165);
lean_inc_ref(x_24);
x_202 = lean_array_push(x_201, x_24);
x_203 = lean_array_push(x_202, x_76);
x_204 = lean_array_push(x_203, x_77);
lean_inc_ref(x_24);
x_205 = lean_array_push(x_204, x_24);
x_206 = lean_array_push(x_205, x_197);
x_207 = lean_array_push(x_206, x_24);
x_208 = lean_array_push(x_207, x_200);
x_209 = lean_array_push(x_208, x_46);
x_210 = lean_array_push(x_209, x_146);
lean_inc(x_5);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_5);
lean_ctor_set(x_211, 1, x_74);
lean_ctor_set(x_211, 2, x_210);
x_212 = l_Lean_Syntax_node4(x_5, x_9, x_72, x_158, x_195, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_3);
return x_213;
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Command_registerSimpAttr___closed__7 = _init_l_Lean_Parser_Command_registerSimpAttr___closed__7();
lean_mark_persistent(l_Lean_Parser_Command_registerSimpAttr___closed__7);
l_Lean_Parser_Command_registerSimpAttr___closed__23 = _init_l_Lean_Parser_Command_registerSimpAttr___closed__23();
lean_mark_persistent(l_Lean_Parser_Command_registerSimpAttr___closed__23);
l_Lean_Parser_Command_registerSimpAttr = _init_l_Lean_Parser_Command_registerSimpAttr();
lean_mark_persistent(l_Lean_Parser_Command_registerSimpAttr);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__123 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__123();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__123);
l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__124 = _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__124();
lean_mark_persistent(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__124);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
