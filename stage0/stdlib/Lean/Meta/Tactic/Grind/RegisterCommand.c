// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.RegisterCommand
// Imports: public meta import Lean.Meta.Tactic.Grind.Attr
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(127, 104, 105, 89, 118, 166, 50, 151)}};
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_3),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 191, 239, 115, 53, 206, 180, 232)}};
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_4),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(107, 172, 234, 152, 52, 83, 123, 128)}};
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_6 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_5),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(218, 209, 178, 101, 134, 255, 253, 170)}};
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_6),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 227, 95, 237, 217, 20, 89, 120)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__7 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value;
static const lean_string_object l_Lean_Parser_Command_registerGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__8 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__8_value;
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
static const lean_ctor_object l_Lean_Parser_Command_registerGrindAttr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__7_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__22_value)}};
static const lean_object* l_Lean_Parser_Command_registerGrindAttr___closed__23 = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Command_registerGrindAttr = (const lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_\?"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(19, 110, 207, 78, 164, 149, 1, 207)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Parser.Attr.grindMod"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value;
static lean_once_cell_t l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 207, 35, 177, 108, 73, 87)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(124, 247, 59, 43, 44, 177, 111, 66)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(113, 140, 114, 135, 71, 133, 96, 5)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(241, 12, 90, 240, 78, 252, 149, 89)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value;
static lean_once_cell_t l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(65, 184, 222, 195, 211, 23, 22, 1)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(222, 145, 103, 225, 142, 169, 142, 153)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "registerAttr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value;
static lean_once_cell_t l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(98, 25, 4, 98, 170, 222, 222, 42)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(213, 19, 34, 154, 74, 108, 206, 181)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_1),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value;
static const lean_string_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value;
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerGrindAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_2),((lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value;
static lean_once_cell_t l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78;
static const lean_array_object l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79 = (const lean_object*)&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18));
v___x_92_ = l_String_toRawSubstring_x27(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21));
v___x_97_ = l_String_toRawSubstring_x27(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24));
v___x_101_ = l_String_toRawSubstring_x27(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33));
v___x_124_ = l_String_toRawSubstring_x27(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40));
v___x_137_ = l_String_toRawSubstring_x27(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57));
v___x_183_ = l_String_toRawSubstring_x27(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78(void){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Array_mkArray0(lean_box(0));
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1(lean_object* v_x_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_234_ = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__0));
v___x_235_ = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__4));
v___x_447_ = ((lean_object*)(l_Lean_Parser_Command_registerGrindAttr___closed__7));
lean_inc(v_x_231_);
v___x_448_ = l_Lean_Syntax_isOfKind(v_x_231_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v_x_231_);
v___x_449_ = lean_box(1);
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_a_233_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_id_454_; lean_object* v___y_456_; lean_object* v___x_491_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = l_Lean_Syntax_getArg(v_x_231_, v___x_451_);
v___x_453_ = lean_unsigned_to_nat(2u);
v_id_454_ = l_Lean_Syntax_getArg(v_x_231_, v___x_453_);
lean_dec(v_x_231_);
v___x_491_ = l_Lean_Syntax_getOptional_x3f(v___x_452_);
lean_dec(v___x_452_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
v___y_456_ = v___x_492_;
goto v___jp_455_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_val_493_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_491_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v___x_491_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_val_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
v___y_456_ = v___x_498_;
goto v___jp_455_;
}
}
}
v___jp_455_:
{
lean_object* v___x_457_; lean_object* v_str1_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; lean_object* v_idParser1_463_; lean_object* v___x_464_; lean_object* v_str2_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_idParser2_468_; lean_object* v___x_469_; lean_object* v_str3_470_; lean_object* v_quotContext_471_; lean_object* v_currMacroScope_472_; lean_object* v_ref_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_idParser3_476_; lean_object* v___x_477_; lean_object* v_str4_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_idParser4_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_457_ = l_Lean_TSyntax_getId(v_id_454_);
lean_inc_n(v___x_457_, 5);
v_str1_458_ = l_Lean_Name_toString(v___x_457_, v___x_448_);
v___x_459_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67));
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68));
v___x_461_ = l_Lean_Name_append(v___x_460_, v___x_457_);
v___x_462_ = 0;
v_idParser1_463_ = l_Lean_mkIdentFrom(v_id_454_, v___x_461_, v___x_462_);
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69));
lean_inc_ref_n(v_str1_458_, 3);
v_str2_465_ = lean_string_append(v_str1_458_, v___x_464_);
v___x_466_ = lean_name_append_after(v___x_457_, v___x_464_);
v___x_467_ = l_Lean_Name_append(v___x_460_, v___x_466_);
v_idParser2_468_ = l_Lean_mkIdentFrom(v_id_454_, v___x_467_, v___x_462_);
v___x_469_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70));
v_str3_470_ = lean_string_append(v_str1_458_, v___x_469_);
v_quotContext_471_ = lean_ctor_get(v_a_232_, 1);
v_currMacroScope_472_ = lean_ctor_get(v_a_232_, 2);
v_ref_473_ = lean_ctor_get(v_a_232_, 5);
v___x_474_ = lean_name_append_after(v___x_457_, v___x_469_);
v___x_475_ = l_Lean_Name_append(v___x_460_, v___x_474_);
v_idParser3_476_ = l_Lean_mkIdentFrom(v_id_454_, v___x_475_, v___x_462_);
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71));
v_str4_478_ = lean_string_append(v_str1_458_, v___x_477_);
v___x_479_ = lean_name_append_after(v___x_457_, v___x_477_);
v___x_480_ = l_Lean_Name_append(v___x_460_, v___x_479_);
v_idParser4_481_ = l_Lean_mkIdentFrom(v_id_454_, v___x_480_, v___x_462_);
lean_dec(v_id_454_);
v___x_482_ = l_Lean_SourceInfo_fromRef(v_ref_473_, v___x_462_);
v___x_483_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73));
v___x_484_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74));
v___x_485_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75));
v___x_486_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77));
v___x_487_ = lean_obj_once(&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78, &l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78_once, _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78);
if (lean_obj_tag(v___y_456_) == 1)
{
lean_object* v_val_488_; lean_object* v___x_489_; 
v_val_488_ = lean_ctor_get(v___y_456_, 0);
lean_inc(v_val_488_);
lean_dec_ref(v___y_456_);
v___x_489_ = l_Array_mkArray1___redArg(v_val_488_);
v___y_369_ = v___x_459_;
v___y_370_ = v___x_469_;
v___y_371_ = v___x_484_;
v___y_372_ = v_currMacroScope_472_;
v___y_373_ = v___x_483_;
v___y_374_ = v_idParser4_481_;
v___y_375_ = v___x_482_;
v___y_376_ = v_str1_458_;
v___y_377_ = v___x_486_;
v___y_378_ = v_idParser3_476_;
v___y_379_ = v___x_485_;
v___y_380_ = v_quotContext_471_;
v___y_381_ = v_str4_478_;
v___y_382_ = v___x_457_;
v___y_383_ = v_idParser2_468_;
v___y_384_ = v_str3_470_;
v___y_385_ = v_str2_465_;
v___y_386_ = v___x_487_;
v___y_387_ = v_idParser1_463_;
v___y_388_ = v___x_489_;
goto v___jp_368_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v___y_456_);
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79));
v___y_369_ = v___x_459_;
v___y_370_ = v___x_469_;
v___y_371_ = v___x_484_;
v___y_372_ = v_currMacroScope_472_;
v___y_373_ = v___x_483_;
v___y_374_ = v_idParser4_481_;
v___y_375_ = v___x_482_;
v___y_376_ = v_str1_458_;
v___y_377_ = v___x_486_;
v___y_378_ = v_idParser3_476_;
v___y_379_ = v___x_485_;
v___y_380_ = v_quotContext_471_;
v___y_381_ = v_str4_478_;
v___y_382_ = v___x_457_;
v___y_383_ = v_idParser2_468_;
v___y_384_ = v_str3_470_;
v___y_385_ = v_str2_465_;
v___y_386_ = v___x_487_;
v___y_387_ = v_idParser1_463_;
v___y_388_ = v___x_490_;
goto v___jp_368_;
}
}
}
v___jp_236_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_inc_n(v___y_256_, 12);
lean_inc_n(v___y_260_, 42);
v___x_267_ = l_Lean_Syntax_node1(v___y_260_, v___y_256_, v___y_266_);
lean_inc(v___y_244_);
v___x_268_ = l_Lean_Syntax_node2(v___y_260_, v___y_244_, v___y_241_, v___x_267_);
lean_inc(v___y_255_);
v___x_269_ = l_Lean_Syntax_node1(v___y_260_, v___y_255_, v___x_268_);
lean_inc_n(v___y_251_, 9);
lean_inc(v___y_253_);
v___x_270_ = l_Lean_Syntax_node2(v___y_260_, v___y_253_, v___x_269_, v___y_251_);
v___x_271_ = l_Lean_Syntax_node1(v___y_260_, v___y_256_, v___x_270_);
lean_inc(v___y_239_);
v___x_272_ = l_Lean_Syntax_node1(v___y_260_, v___y_239_, v___x_271_);
lean_inc(v___y_262_);
v___x_273_ = l_Lean_Syntax_node4(v___y_260_, v___y_262_, v___y_247_, v___y_254_, v___y_240_, v___x_272_);
v___x_274_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0));
v___x_275_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1));
v___x_276_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2));
lean_inc_ref(v___y_265_);
v___x_277_ = l_Lean_Name_mkStr4(v___x_234_, v___x_235_, v___y_265_, v___x_276_);
v___x_278_ = l_Lean_Syntax_node1(v___y_260_, v___x_277_, v___y_251_);
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___y_260_);
lean_ctor_set(v___x_279_, 1, v___x_274_);
v___x_280_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4));
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5));
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v___y_260_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6));
v___x_284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_284_, 0, v___y_260_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7));
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_260_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8));
v___x_288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_288_, 0, v___y_260_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
lean_inc_ref_n(v___x_288_, 4);
lean_inc_ref_n(v___x_286_, 3);
lean_inc_ref_n(v___x_284_, 3);
lean_inc_ref_n(v___x_282_, 4);
v___x_289_ = l_Lean_Syntax_node5(v___y_260_, v___x_280_, v___x_282_, v___x_284_, v___x_286_, v___y_250_, v___x_288_);
v___x_290_ = l_Lean_Syntax_node1(v___y_260_, v___y_256_, v___x_289_);
v___x_291_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11));
v___x_292_ = lean_box(2);
v___x_293_ = l_Lean_Syntax_mkStrLit(v___y_242_, v___x_292_);
v___x_294_ = l_Lean_Syntax_node1(v___y_260_, v___x_291_, v___x_293_);
v___x_295_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13));
v___x_296_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15));
v___x_297_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17));
v___x_298_ = lean_obj_once(&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19, &l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_once, _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19);
v___x_299_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20));
lean_inc_n(v___y_238_, 3);
lean_inc_n(v___y_263_, 3);
v___x_300_ = l_Lean_addMacroScope(v___y_263_, v___x_299_, v___y_238_);
lean_inc_n(v___y_259_, 2);
v___x_301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_301_, 0, v___y_260_);
lean_ctor_set(v___x_301_, 1, v___x_298_);
lean_ctor_set(v___x_301_, 2, v___x_300_);
lean_ctor_set(v___x_301_, 3, v___y_259_);
v___x_302_ = l_Lean_Syntax_node2(v___y_260_, v___x_297_, v___x_301_, v___y_251_);
v___x_303_ = lean_obj_once(&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22, &l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22_once, _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22);
v___x_304_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23));
lean_inc_ref(v___y_237_);
v___x_305_ = l_Lean_Name_mkStr4(v___x_234_, v___x_235_, v___y_237_, v___x_304_);
lean_inc(v___x_305_);
v___x_306_ = l_Lean_addMacroScope(v___y_263_, v___x_305_, v___y_238_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___y_261_);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___y_259_);
v___x_309_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_309_, 0, v___y_260_);
lean_ctor_set(v___x_309_, 1, v___x_303_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
lean_ctor_set(v___x_309_, 3, v___x_308_);
v___x_310_ = l_Lean_Syntax_node2(v___y_260_, v___x_297_, v___x_309_, v___y_251_);
v___x_311_ = l_Lean_Syntax_node2(v___y_260_, v___y_256_, v___x_302_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node3(v___y_260_, v___x_296_, v___x_282_, v___x_311_, v___x_288_);
v___x_313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_313_, 0, v___y_260_);
lean_ctor_set(v___x_313_, 1, v___y_252_);
v___x_314_ = l_Lean_Syntax_node2(v___y_260_, v___x_295_, v___x_312_, v___x_313_);
lean_inc_n(v___x_314_, 3);
v___x_315_ = l_Lean_Syntax_node2(v___y_260_, v___y_256_, v___x_294_, v___x_314_);
v___x_316_ = lean_obj_once(&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25, &l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_once, _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25);
v___x_317_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26));
v___x_318_ = l_Lean_addMacroScope(v___y_263_, v___x_317_, v___y_238_);
v___x_319_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_319_, 0, v___y_260_);
lean_ctor_set(v___x_319_, 1, v___x_316_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v___y_259_);
v___x_320_ = lean_unsigned_to_nat(10u);
v___x_321_ = lean_mk_empty_array_with_capacity(v___x_320_);
v___x_322_ = lean_array_push(v___x_321_, v___y_257_);
v___x_323_ = lean_array_push(v___x_322_, v___y_251_);
v___x_324_ = lean_array_push(v___x_323_, v___x_278_);
v___x_325_ = lean_array_push(v___x_324_, v___x_279_);
v___x_326_ = lean_array_push(v___x_325_, v___y_251_);
lean_inc_ref_n(v___x_326_, 3);
v___x_327_ = lean_array_push(v___x_326_, v___x_290_);
v___x_328_ = lean_array_push(v___x_327_, v___y_251_);
v___x_329_ = lean_array_push(v___x_328_, v___x_315_);
lean_inc_n(v___y_248_, 3);
v___x_330_ = lean_array_push(v___x_329_, v___y_248_);
lean_inc_ref_n(v___x_319_, 3);
v___x_331_ = lean_array_push(v___x_330_, v___x_319_);
v___x_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_332_, 0, v___y_260_);
lean_ctor_set(v___x_332_, 1, v___x_275_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = l_Lean_Syntax_node5(v___y_260_, v___x_280_, v___x_282_, v___x_284_, v___x_286_, v___y_246_, v___x_288_);
v___x_334_ = l_Lean_Syntax_node1(v___y_260_, v___y_256_, v___x_333_);
v___x_335_ = l_Lean_Syntax_mkStrLit(v___y_249_, v___x_292_);
v___x_336_ = l_Lean_Syntax_node1(v___y_260_, v___x_291_, v___x_335_);
v___x_337_ = l_Lean_Syntax_node2(v___y_260_, v___y_256_, v___x_336_, v___x_314_);
v___x_338_ = lean_array_push(v___x_326_, v___x_334_);
v___x_339_ = lean_array_push(v___x_338_, v___y_251_);
v___x_340_ = lean_array_push(v___x_339_, v___x_337_);
v___x_341_ = lean_array_push(v___x_340_, v___y_248_);
v___x_342_ = lean_array_push(v___x_341_, v___x_319_);
v___x_343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_343_, 0, v___y_260_);
lean_ctor_set(v___x_343_, 1, v___x_275_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
v___x_344_ = l_Lean_Syntax_node5(v___y_260_, v___x_280_, v___x_282_, v___x_284_, v___x_286_, v___y_243_, v___x_288_);
v___x_345_ = l_Lean_Syntax_node1(v___y_260_, v___y_256_, v___x_344_);
v___x_346_ = l_Lean_Syntax_mkStrLit(v___y_264_, v___x_292_);
v___x_347_ = l_Lean_Syntax_node1(v___y_260_, v___x_291_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node2(v___y_260_, v___y_256_, v___x_347_, v___x_314_);
v___x_349_ = lean_array_push(v___x_326_, v___x_345_);
v___x_350_ = lean_array_push(v___x_349_, v___y_251_);
v___x_351_ = lean_array_push(v___x_350_, v___x_348_);
v___x_352_ = lean_array_push(v___x_351_, v___y_248_);
v___x_353_ = lean_array_push(v___x_352_, v___x_319_);
v___x_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_354_, 0, v___y_260_);
lean_ctor_set(v___x_354_, 1, v___x_275_);
lean_ctor_set(v___x_354_, 2, v___x_353_);
v___x_355_ = l_Lean_Syntax_node5(v___y_260_, v___x_280_, v___x_282_, v___x_284_, v___x_286_, v___y_258_, v___x_288_);
v___x_356_ = l_Lean_Syntax_node1(v___y_260_, v___y_256_, v___x_355_);
v___x_357_ = l_Lean_Syntax_mkStrLit(v___y_245_, v___x_292_);
v___x_358_ = l_Lean_Syntax_node1(v___y_260_, v___x_291_, v___x_357_);
v___x_359_ = l_Lean_Syntax_node2(v___y_260_, v___y_256_, v___x_358_, v___x_314_);
v___x_360_ = lean_array_push(v___x_326_, v___x_356_);
v___x_361_ = lean_array_push(v___x_360_, v___y_251_);
v___x_362_ = lean_array_push(v___x_361_, v___x_359_);
v___x_363_ = lean_array_push(v___x_362_, v___y_248_);
v___x_364_ = lean_array_push(v___x_363_, v___x_319_);
v___x_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_365_, 0, v___y_260_);
lean_ctor_set(v___x_365_, 1, v___x_275_);
lean_ctor_set(v___x_365_, 2, v___x_364_);
v___x_366_ = l_Lean_Syntax_node5(v___y_260_, v___y_256_, v___x_273_, v___x_332_, v___x_343_, v___x_354_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_a_233_);
return v___x_367_;
}
v___jp_368_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_inc_ref_n(v___y_386_, 2);
v___x_389_ = l_Array_append___redArg(v___y_386_, v___y_388_);
lean_dec_ref(v___y_388_);
lean_inc_n(v___y_373_, 5);
lean_inc_n(v___y_375_, 18);
v___x_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_390_, 0, v___y_375_);
lean_ctor_set(v___x_390_, 1, v___y_373_);
lean_ctor_set(v___x_390_, 2, v___x_389_);
v___x_391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_391_, 0, v___y_375_);
lean_ctor_set(v___x_391_, 1, v___y_373_);
lean_ctor_set(v___x_391_, 2, v___y_386_);
v___x_392_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27));
v___x_393_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28));
v___x_394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_394_, 0, v___y_375_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
v___x_395_ = l_Lean_Syntax_node1(v___y_375_, v___x_393_, v___x_394_);
v___x_396_ = l_Lean_Syntax_node1(v___y_375_, v___y_373_, v___x_395_);
v___x_397_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29));
v___x_398_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30));
v___x_399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_399_, 0, v___y_375_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
v___x_400_ = l_Lean_Syntax_node1(v___y_375_, v___x_398_, v___x_399_);
v___x_401_ = l_Lean_Syntax_node1(v___y_375_, v___y_373_, v___x_400_);
lean_inc_ref_n(v___x_391_, 4);
lean_inc_ref(v___x_390_);
lean_inc(v___y_377_);
v___x_402_ = l_Lean_Syntax_node7(v___y_375_, v___y_377_, v___x_390_, v___x_391_, v___x_396_, v___x_391_, v___x_401_, v___x_391_, v___x_391_);
v___x_403_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32));
lean_inc_ref(v___y_371_);
v___x_404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_404_, 0, v___y_375_);
lean_ctor_set(v___x_404_, 1, v___y_371_);
v___x_405_ = l_Lean_Syntax_node1(v___y_375_, v___x_403_, v___x_404_);
v___x_406_ = lean_obj_once(&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34, &l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34_once, _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34);
v___x_407_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35));
lean_inc_n(v___y_372_, 3);
lean_inc_n(v___y_380_, 3);
v___x_408_ = l_Lean_addMacroScope(v___y_380_, v___x_407_, v___y_372_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_410_, 0, v___y_375_);
lean_ctor_set(v___x_410_, 1, v___x_406_);
lean_ctor_set(v___x_410_, 2, v___x_408_);
lean_ctor_set(v___x_410_, 3, v___x_409_);
v___x_411_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36));
v___x_412_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38));
v___x_413_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39));
v___x_414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_414_, 0, v___y_375_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_obj_once(&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41, &l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_once, _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41);
v___x_416_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42));
v___x_417_ = l_Lean_addMacroScope(v___y_380_, v___x_416_, v___y_372_);
v___x_418_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47));
v___x_419_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_419_, 0, v___y_375_);
lean_ctor_set(v___x_419_, 1, v___x_415_);
lean_ctor_set(v___x_419_, 2, v___x_417_);
lean_ctor_set(v___x_419_, 3, v___x_418_);
lean_inc_ref(v___x_414_);
v___x_420_ = l_Lean_Syntax_node2(v___y_375_, v___x_412_, v___x_414_, v___x_419_);
v___x_421_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48));
v___x_422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_422_, 0, v___y_375_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_Syntax_node3(v___y_375_, v___y_373_, v___x_410_, v___x_420_, v___x_422_);
v___x_424_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50));
v___x_425_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52));
v___x_426_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54));
v___x_427_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56));
v___x_428_ = lean_obj_once(&l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58, &l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58_once, _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58);
v___x_429_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59));
v___x_430_ = l_Lean_addMacroScope(v___y_380_, v___x_429_, v___y_372_);
v___x_431_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62));
v___x_432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_432_, 0, v___y_375_);
lean_ctor_set(v___x_432_, 1, v___x_428_);
lean_ctor_set(v___x_432_, 2, v___x_430_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
lean_inc(v___y_382_);
v___x_433_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_409_, v___y_382_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_quoteNameMk(v___y_382_);
v___y_237_ = v___y_369_;
v___y_238_ = v___y_372_;
v___y_239_ = v___x_424_;
v___y_240_ = v___x_423_;
v___y_241_ = v___x_432_;
v___y_242_ = v___y_376_;
v___y_243_ = v___y_378_;
v___y_244_ = v___x_427_;
v___y_245_ = v___y_381_;
v___y_246_ = v___y_383_;
v___y_247_ = v___x_402_;
v___y_248_ = v___x_414_;
v___y_249_ = v___y_385_;
v___y_250_ = v___y_387_;
v___y_251_ = v___x_391_;
v___y_252_ = v___y_370_;
v___y_253_ = v___x_425_;
v___y_254_ = v___x_405_;
v___y_255_ = v___x_426_;
v___y_256_ = v___y_373_;
v___y_257_ = v___x_390_;
v___y_258_ = v___y_374_;
v___y_259_ = v___x_409_;
v___y_260_ = v___y_375_;
v___y_261_ = v___x_409_;
v___y_262_ = v___y_379_;
v___y_263_ = v___y_380_;
v___y_264_ = v___y_384_;
v___y_265_ = v___x_411_;
v___y_266_ = v___x_434_;
goto v___jp_236_;
}
else
{
lean_object* v_val_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v___y_382_);
v_val_435_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_435_);
lean_dec_ref(v___x_433_);
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64));
v___x_437_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65));
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66));
v___x_439_ = lean_string_intercalate(v___x_438_, v_val_435_);
v___x_440_ = lean_string_append(v___x_437_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = lean_box(2);
v___x_442_ = l_Lean_Syntax_mkNameLit(v___x_440_, v___x_441_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_mk_empty_array_with_capacity(v___x_443_);
v___x_445_ = lean_array_push(v___x_444_, v___x_442_);
v___x_446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_441_);
lean_ctor_set(v___x_446_, 1, v___x_436_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
v___y_237_ = v___y_369_;
v___y_238_ = v___y_372_;
v___y_239_ = v___x_424_;
v___y_240_ = v___x_423_;
v___y_241_ = v___x_432_;
v___y_242_ = v___y_376_;
v___y_243_ = v___y_378_;
v___y_244_ = v___x_427_;
v___y_245_ = v___y_381_;
v___y_246_ = v___y_383_;
v___y_247_ = v___x_402_;
v___y_248_ = v___x_414_;
v___y_249_ = v___y_385_;
v___y_250_ = v___y_387_;
v___y_251_ = v___x_391_;
v___y_252_ = v___y_370_;
v___y_253_ = v___x_425_;
v___y_254_ = v___x_405_;
v___y_255_ = v___x_426_;
v___y_256_ = v___y_373_;
v___y_257_ = v___x_390_;
v___y_258_ = v___y_374_;
v___y_259_ = v___x_409_;
v___y_260_ = v___y_375_;
v___y_261_ = v___x_409_;
v___y_262_ = v___y_379_;
v___y_263_ = v___y_380_;
v___y_264_ = v___y_384_;
v___y_265_ = v___x_411_;
v___y_266_ = v___x_446_;
goto v___jp_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___boxed(lean_object* v_x_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1(v_x_501_, v_a_502_, v_a_503_);
lean_dec_ref(v_a_502_);
return v_res_504_;
}
}
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
}
#ifdef __cplusplus
}
#endif
