// Lean compiler output
// Module: Lean.Elab.Mixfix
// Imports: public import Lean.Elab.Attributes import Init.Syntax
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
extern lean_object* l_Lean_Elab_mkAttrKindGlobal;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "identPrec"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 25, 252, 182, 120, 175, 78, 126)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__6;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(106, 194, 158, 37, 173, 85, 64, 87)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lhs"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__11;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(246, 90, 165, 168, 14, 148, 243, 73)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__14;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(149, 22, 109, 211, 70, 26, 115, 13)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mixfix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(1, 31, 80, 86, 44, 46, 155, 0)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__21 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__22 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__23 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value;
static const lean_array_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__24 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__25 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__26 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__27 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__28 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__29 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__30 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__31 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__32 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__33 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__34 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__35 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value;
static lean_once_cell_t l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__36;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__37 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__38 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__39 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "infixl"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__40 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value),LEAN_SCALAR_PTR_LITERAL(118, 176, 144, 146, 48, 231, 100, 173)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__41 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "infix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__42 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value),LEAN_SCALAR_PTR_LITERAL(8, 202, 116, 85, 196, 237, 101, 141)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__43 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "infixr"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__44 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value),LEAN_SCALAR_PTR_LITERAL(9, 7, 27, 92, 157, 7, 198, 225)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__45 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "prefix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__46 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value),LEAN_SCALAR_PTR_LITERAL(223, 255, 86, 177, 195, 168, 212, 163)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__47 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "postfix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__48 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value),LEAN_SCALAR_PTR_LITERAL(97, 175, 134, 52, 144, 48, 141, 10)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__49 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__50 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__51 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__52 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__53 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__54 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_expandMixfix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_expandMixfix___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_expandMixfix___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "expandMixfix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 127, 199, 109, 87, 154, 161, 211)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object* v_stx_1_, lean_object* v_f_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_attrKind_6_; lean_object* v___x_7_; lean_object* v_stx_8_; lean_object* v___x_9_; 
v___x_5_ = lean_unsigned_to_nat(2u);
v_attrKind_6_ = l_Lean_Syntax_getArg(v_stx_1_, v___x_5_);
v___x_7_ = l_Lean_Elab_mkAttrKindGlobal;
v_stx_8_ = l_Lean_Syntax_setArg(v_stx_1_, v___x_5_, v___x_7_);
v___x_9_ = lean_apply_3(v_f_2_, v_stx_8_, v_a_3_, v_a_4_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
v_a_11_ = lean_ctor_get(v___x_9_, 1);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_19_ == 0)
{
v___x_13_ = v___x_9_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_inc(v_a_10_);
lean_dec(v___x_9_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_15_ = l_Lean_Syntax_setArg(v_a_10_, v___x_5_, v_attrKind_6_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_a_11_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_attrKind_6_);
v_a_20_ = lean_ctor_get(v___x_9_, 0);
v_a_21_ = lean_ctor_get(v___x_9_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_9_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_inc(v_a_20_);
lean_dec(v___x_9_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_20_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5));
v___x_40_ = l_String_toRawSubstring_x27(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10));
v___x_47_ = l_String_toRawSubstring_x27(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13));
v___x_52_ = l_String_toRawSubstring_x27(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Array_mkArray0(lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0(lean_object* v_stx_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_150_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0));
v___x_151_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1));
v___x_422_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17));
lean_inc(v_stx_147_);
v___x_423_ = l_Lean_Syntax_isOfKind(v_stx_147_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_dec_ref(v___y_148_);
lean_dec(v_stx_147_);
v___x_424_ = l_Lean_Macro_throwUnsupported___redArg(v___y_149_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v_prio_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; uint8_t v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v_name_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v_prio_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v_name_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; uint8_t v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v_prio_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_901_; lean_object* v___y_902_; uint8_t v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v_name_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v_prio_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; uint8_t v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v_name_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v_prio_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v_name_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v_attrs_x3f_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v_doc_x3f_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_425_);
v___x_1422_ = l_Lean_Syntax_isNone(v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1421_);
v___x_1424_ = l_Lean_Syntax_matchesNull(v___x_1421_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
lean_dec(v___x_1421_);
lean_dec_ref(v___y_148_);
lean_dec(v_stx_147_);
v___x_1425_ = l_Lean_Macro_throwUnsupported___redArg(v___y_149_);
return v___x_1425_;
}
else
{
lean_object* v_doc_x3f_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_doc_x3f_1426_ = l_Lean_Syntax_getArg(v___x_1421_, v___x_425_);
lean_dec(v___x_1421_);
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54));
lean_inc(v_doc_x3f_1426_);
v___x_1428_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_doc_x3f_1426_);
lean_dec_ref(v___y_148_);
lean_dec(v_stx_147_);
v___x_1429_ = l_Lean_Macro_throwUnsupported___redArg(v___y_149_);
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_doc_x3f_1426_);
v_doc_x3f_1405_ = v___x_1430_;
v___y_1406_ = v___y_148_;
v___y_1407_ = v___y_149_;
goto v___jp_1404_;
}
}
}
else
{
lean_object* v___x_1431_; 
lean_dec(v___x_1421_);
v___x_1431_ = lean_box(0);
v_doc_x3f_1405_ = v___x_1431_;
v___y_1406_ = v___y_148_;
v___y_1407_ = v___y_149_;
goto v___jp_1404_;
}
v___jp_426_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_inc_ref(v___y_441_);
v___x_444_ = l_Array_append___redArg(v___y_441_, v___y_443_);
lean_dec_ref(v___y_443_);
lean_inc(v___y_437_);
lean_inc(v___y_429_);
v___x_445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_445_, 0, v___y_429_);
lean_ctor_set(v___x_445_, 1, v___y_437_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
if (lean_obj_tag(v___y_438_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_val_446_ = lean_ctor_get(v___y_438_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v___y_438_);
v___x_447_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_448_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_429_);
v___x_449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_429_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(v___y_429_);
v___x_451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_429_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_429_);
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___y_429_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_429_);
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___y_429_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
lean_inc(v___y_429_);
v___x_456_ = l_Lean_Syntax_node5(v___y_429_, v___x_447_, v___x_449_, v___x_451_, v___x_453_, v_val_446_, v___x_455_);
v___x_457_ = l_Array_mkArray1___redArg(v___x_456_);
v___y_153_ = v___y_427_;
v___y_154_ = v___y_428_;
v___y_155_ = v___y_429_;
v___y_156_ = v___y_430_;
v___y_157_ = v___y_431_;
v___y_158_ = v___y_432_;
v___y_159_ = v___y_433_;
v___y_160_ = v___y_434_;
v___y_161_ = v___y_435_;
v___y_162_ = v___y_436_;
v___y_163_ = v___y_437_;
v___y_164_ = v___y_439_;
v___y_165_ = v___y_440_;
v___y_166_ = v___x_445_;
v___y_167_ = v___y_441_;
v___y_168_ = v___y_442_;
v___y_169_ = v___x_457_;
goto v___jp_152_;
}
else
{
lean_object* v___x_458_; 
lean_dec(v___y_438_);
v___x_458_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_153_ = v___y_427_;
v___y_154_ = v___y_428_;
v___y_155_ = v___y_429_;
v___y_156_ = v___y_430_;
v___y_157_ = v___y_431_;
v___y_158_ = v___y_432_;
v___y_159_ = v___y_433_;
v___y_160_ = v___y_434_;
v___y_161_ = v___y_435_;
v___y_162_ = v___y_436_;
v___y_163_ = v___y_437_;
v___y_164_ = v___y_439_;
v___y_165_ = v___y_440_;
v___y_166_ = v___x_445_;
v___y_167_ = v___y_441_;
v___y_168_ = v___y_442_;
v___y_169_ = v___x_458_;
goto v___jp_152_;
}
}
v___jp_459_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc_ref(v___y_475_);
v___x_478_ = l_Array_append___redArg(v___y_475_, v___y_477_);
lean_dec_ref(v___y_477_);
lean_inc(v___y_471_);
lean_inc(v___y_464_);
v___x_479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_479_, 0, v___y_464_);
lean_ctor_set(v___x_479_, 1, v___y_471_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_471_);
lean_inc(v___y_464_);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v___y_464_);
lean_ctor_set(v___x_480_, 1, v___y_471_);
lean_ctor_set(v___x_480_, 2, v___y_475_);
lean_inc(v___y_464_);
v___x_481_ = l_Lean_Syntax_node1(v___y_464_, v___y_460_, v___x_480_);
lean_inc(v___y_464_);
v___x_482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_482_, 0, v___y_464_);
lean_ctor_set(v___x_482_, 1, v___y_461_);
v___x_483_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(v___y_464_);
v___x_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_464_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
lean_inc(v___y_464_);
v___x_485_ = l_Lean_Syntax_node2(v___y_464_, v___y_463_, v___x_484_, v___y_470_);
lean_inc(v___y_471_);
lean_inc(v___y_464_);
v___x_486_ = l_Lean_Syntax_node1(v___y_464_, v___y_471_, v___x_485_);
if (lean_obj_tag(v___y_474_) == 1)
{
lean_object* v_val_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_val_487_ = lean_ctor_get(v___y_474_, 0);
lean_inc(v_val_487_);
lean_dec_ref(v___y_474_);
v___x_488_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_489_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_464_);
v___x_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_490_, 0, v___y_464_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(v___y_464_);
v___x_492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_492_, 0, v___y_464_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_464_);
v___x_494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_464_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_464_);
v___x_496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_496_, 0, v___y_464_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
lean_inc(v___y_464_);
v___x_497_ = l_Lean_Syntax_node5(v___y_464_, v___x_488_, v___x_490_, v___x_492_, v___x_494_, v_val_487_, v___x_496_);
v___x_498_ = l_Array_mkArray1___redArg(v___x_497_);
v___y_427_ = v___x_486_;
v___y_428_ = v___y_462_;
v___y_429_ = v___y_464_;
v___y_430_ = v___y_465_;
v___y_431_ = v___y_466_;
v___y_432_ = v___y_467_;
v___y_433_ = v___y_468_;
v___y_434_ = v___y_469_;
v___y_435_ = v___x_479_;
v___y_436_ = v___x_482_;
v___y_437_ = v___y_471_;
v___y_438_ = v___y_472_;
v___y_439_ = v___x_481_;
v___y_440_ = v___y_473_;
v___y_441_ = v___y_475_;
v___y_442_ = v___y_476_;
v___y_443_ = v___x_498_;
goto v___jp_426_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v___y_474_);
v___x_499_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_427_ = v___x_486_;
v___y_428_ = v___y_462_;
v___y_429_ = v___y_464_;
v___y_430_ = v___y_465_;
v___y_431_ = v___y_466_;
v___y_432_ = v___y_467_;
v___y_433_ = v___y_468_;
v___y_434_ = v___y_469_;
v___y_435_ = v___x_479_;
v___y_436_ = v___x_482_;
v___y_437_ = v___y_471_;
v___y_438_ = v___y_472_;
v___y_439_ = v___x_481_;
v___y_440_ = v___y_473_;
v___y_441_ = v___y_475_;
v___y_442_ = v___y_476_;
v___y_443_ = v___x_499_;
goto v___jp_426_;
}
}
v___jp_500_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_inc_ref(v___y_517_);
v___x_519_ = l_Array_append___redArg(v___y_517_, v___y_518_);
lean_dec_ref(v___y_518_);
lean_inc(v___y_513_);
lean_inc(v___y_505_);
v___x_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_520_, 0, v___y_505_);
lean_ctor_set(v___x_520_, 1, v___y_513_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
if (lean_obj_tag(v___y_511_) == 1)
{
lean_object* v_val_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_val_521_ = lean_ctor_get(v___y_511_, 0);
lean_inc(v_val_521_);
lean_dec_ref(v___y_511_);
v___x_522_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_506_);
v___x_523_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_506_, v___x_522_);
v___x_524_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(v___y_505_);
v___x_525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_525_, 0, v___y_505_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_inc_ref(v___y_517_);
v___x_526_ = l_Array_append___redArg(v___y_517_, v_val_521_);
lean_dec(v_val_521_);
lean_inc(v___y_513_);
lean_inc(v___y_505_);
v___x_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_527_, 0, v___y_505_);
lean_ctor_set(v___x_527_, 1, v___y_513_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
v___x_528_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(v___y_505_);
v___x_529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_505_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_inc(v___y_505_);
v___x_530_ = l_Lean_Syntax_node3(v___y_505_, v___x_523_, v___x_525_, v___x_527_, v___x_529_);
v___x_531_ = l_Array_mkArray1___redArg(v___x_530_);
v___y_460_ = v___y_501_;
v___y_461_ = v___y_502_;
v___y_462_ = v___y_503_;
v___y_463_ = v___y_504_;
v___y_464_ = v___y_505_;
v___y_465_ = v___y_506_;
v___y_466_ = v___y_507_;
v___y_467_ = v___y_508_;
v___y_468_ = v___y_509_;
v___y_469_ = v___y_510_;
v___y_470_ = v___y_512_;
v___y_471_ = v___y_513_;
v___y_472_ = v___y_514_;
v___y_473_ = v___y_515_;
v___y_474_ = v___y_516_;
v___y_475_ = v___y_517_;
v___y_476_ = v___x_520_;
v___y_477_ = v___x_531_;
goto v___jp_459_;
}
else
{
lean_object* v___x_532_; 
lean_dec(v___y_511_);
v___x_532_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_460_ = v___y_501_;
v___y_461_ = v___y_502_;
v___y_462_ = v___y_503_;
v___y_463_ = v___y_504_;
v___y_464_ = v___y_505_;
v___y_465_ = v___y_506_;
v___y_466_ = v___y_507_;
v___y_467_ = v___y_508_;
v___y_468_ = v___y_509_;
v___y_469_ = v___y_510_;
v___y_470_ = v___y_512_;
v___y_471_ = v___y_513_;
v___y_472_ = v___y_514_;
v___y_473_ = v___y_515_;
v___y_474_ = v___y_516_;
v___y_475_ = v___y_517_;
v___y_476_ = v___x_520_;
v___y_477_ = v___x_532_;
goto v___jp_459_;
}
}
v___jp_533_:
{
lean_object* v_quotContext_545_; lean_object* v_currMacroScope_546_; lean_object* v_ref_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_quotContext_545_ = lean_ctor_get(v___y_543_, 1);
lean_inc(v_quotContext_545_);
v_currMacroScope_546_ = lean_ctor_get(v___y_543_, 2);
lean_inc(v_currMacroScope_546_);
v_ref_547_ = lean_ctor_get(v___y_543_, 5);
lean_inc(v_ref_547_);
lean_dec_ref(v___y_543_);
v___x_548_ = lean_unsigned_to_nat(7u);
v___x_549_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_548_);
v___x_550_ = lean_unsigned_to_nat(9u);
v___x_551_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_550_);
lean_dec(v_stx_147_);
v___x_552_ = l_Lean_SourceInfo_fromRef(v_ref_547_, v___y_538_);
lean_dec(v_ref_547_);
v___x_553_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_554_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_555_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_556_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_536_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_558_; 
v_val_557_ = lean_ctor_get(v___y_536_, 0);
lean_inc(v_val_557_);
lean_dec_ref(v___y_536_);
v___x_558_ = l_Array_mkArray1___redArg(v_val_557_);
v___y_501_ = v___y_534_;
v___y_502_ = v___x_553_;
v___y_503_ = v___y_544_;
v___y_504_ = v___y_535_;
v___y_505_ = v___x_552_;
v___y_506_ = v___y_537_;
v___y_507_ = v___x_554_;
v___y_508_ = v_quotContext_545_;
v___y_509_ = v_currMacroScope_546_;
v___y_510_ = v___x_551_;
v___y_511_ = v___y_541_;
v___y_512_ = v___y_540_;
v___y_513_ = v___x_555_;
v___y_514_ = v_prio_542_;
v___y_515_ = v___x_549_;
v___y_516_ = v___y_539_;
v___y_517_ = v___x_556_;
v___y_518_ = v___x_558_;
goto v___jp_500_;
}
else
{
lean_object* v___x_559_; 
lean_dec(v___y_536_);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_501_ = v___y_534_;
v___y_502_ = v___x_553_;
v___y_503_ = v___y_544_;
v___y_504_ = v___y_535_;
v___y_505_ = v___x_552_;
v___y_506_ = v___y_537_;
v___y_507_ = v___x_554_;
v___y_508_ = v_quotContext_545_;
v___y_509_ = v_currMacroScope_546_;
v___y_510_ = v___x_551_;
v___y_511_ = v___y_541_;
v___y_512_ = v___y_540_;
v___y_513_ = v___x_555_;
v___y_514_ = v_prio_542_;
v___y_515_ = v___x_549_;
v___y_516_ = v___y_539_;
v___y_517_ = v___x_556_;
v___y_518_ = v___x_559_;
goto v___jp_500_;
}
}
v___jp_560_:
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(6u);
v___x_574_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_573_);
v___x_575_ = l_Lean_Syntax_isNone(v___x_574_);
if (v___x_575_ == 0)
{
uint8_t v___x_576_; 
lean_inc(v___x_574_);
v___x_576_ = l_Lean_Syntax_matchesNull(v___x_574_, v___y_563_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v___x_574_);
lean_dec_ref(v___y_571_);
lean_dec(v_name_570_);
lean_dec(v___y_568_);
lean_dec(v___y_567_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_562_);
lean_dec(v___y_561_);
lean_dec(v_stx_147_);
v___x_577_ = l_Lean_Macro_throwUnsupported___redArg(v___y_572_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_578_ = l_Lean_Syntax_getArg(v___x_574_, v___x_425_);
lean_dec(v___x_574_);
v___x_579_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_578_);
v___x_580_ = l_Lean_Syntax_isOfKind(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec(v___x_578_);
lean_dec_ref(v___y_571_);
lean_dec(v_name_570_);
lean_dec(v___y_568_);
lean_dec(v___y_567_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_562_);
lean_dec(v___y_561_);
lean_dec(v_stx_147_);
v___x_581_ = l_Lean_Macro_throwUnsupported___redArg(v___y_572_);
return v___x_581_;
}
else
{
lean_object* v_prio_582_; lean_object* v___x_583_; 
v_prio_582_ = l_Lean_Syntax_getArg(v___x_578_, v___y_569_);
lean_dec(v___x_578_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v_prio_582_);
v___y_534_ = v___y_561_;
v___y_535_ = v___y_562_;
v___y_536_ = v___y_565_;
v___y_537_ = v___y_564_;
v___y_538_ = v___y_566_;
v___y_539_ = v_name_570_;
v___y_540_ = v___y_568_;
v___y_541_ = v___y_567_;
v_prio_542_ = v___x_583_;
v___y_543_ = v___y_571_;
v___y_544_ = v___y_572_;
goto v___jp_533_;
}
}
}
else
{
lean_object* v___x_584_; 
lean_dec(v___x_574_);
v___x_584_ = lean_box(0);
v___y_534_ = v___y_561_;
v___y_535_ = v___y_562_;
v___y_536_ = v___y_565_;
v___y_537_ = v___y_564_;
v___y_538_ = v___y_566_;
v___y_539_ = v_name_570_;
v___y_540_ = v___y_568_;
v___y_541_ = v___y_567_;
v_prio_542_ = v___x_584_;
v___y_543_ = v___y_571_;
v___y_544_ = v___y_572_;
goto v___jp_533_;
}
}
v___jp_585_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_inc_ref(v___y_600_);
v___x_603_ = l_Array_append___redArg(v___y_600_, v___y_602_);
lean_dec_ref(v___y_602_);
lean_inc(v___y_586_);
lean_inc(v___y_595_);
v___x_604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_604_, 0, v___y_595_);
lean_ctor_set(v___x_604_, 1, v___y_586_);
lean_ctor_set(v___x_604_, 2, v___x_603_);
if (lean_obj_tag(v___y_587_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_val_605_ = lean_ctor_get(v___y_587_, 0);
lean_inc(v_val_605_);
lean_dec_ref(v___y_587_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_607_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_595_);
v___x_608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_608_, 0, v___y_595_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(v___y_595_);
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___y_595_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_595_);
v___x_612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_612_, 0, v___y_595_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_595_);
v___x_614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_614_, 0, v___y_595_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
lean_inc(v___y_595_);
v___x_615_ = l_Lean_Syntax_node5(v___y_595_, v___x_606_, v___x_608_, v___x_610_, v___x_612_, v_val_605_, v___x_614_);
v___x_616_ = l_Array_mkArray1___redArg(v___x_615_);
v___y_201_ = v___y_586_;
v___y_202_ = v___y_588_;
v___y_203_ = v___y_589_;
v___y_204_ = v___x_604_;
v___y_205_ = v___y_590_;
v___y_206_ = v___y_591_;
v___y_207_ = v___y_592_;
v___y_208_ = v___y_593_;
v___y_209_ = v___y_594_;
v___y_210_ = v___y_595_;
v___y_211_ = v___y_596_;
v___y_212_ = v___y_597_;
v___y_213_ = v___y_598_;
v___y_214_ = v___y_599_;
v___y_215_ = v___y_600_;
v___y_216_ = v___y_601_;
v___y_217_ = v___x_616_;
goto v___jp_200_;
}
else
{
lean_object* v___x_617_; 
lean_dec(v___y_587_);
v___x_617_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_201_ = v___y_586_;
v___y_202_ = v___y_588_;
v___y_203_ = v___y_589_;
v___y_204_ = v___x_604_;
v___y_205_ = v___y_590_;
v___y_206_ = v___y_591_;
v___y_207_ = v___y_592_;
v___y_208_ = v___y_593_;
v___y_209_ = v___y_594_;
v___y_210_ = v___y_595_;
v___y_211_ = v___y_596_;
v___y_212_ = v___y_597_;
v___y_213_ = v___y_598_;
v___y_214_ = v___y_599_;
v___y_215_ = v___y_600_;
v___y_216_ = v___y_601_;
v___y_217_ = v___x_617_;
goto v___jp_200_;
}
}
v___jp_618_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_inc_ref(v___y_633_);
v___x_637_ = l_Array_append___redArg(v___y_633_, v___y_636_);
lean_dec_ref(v___y_636_);
lean_inc(v___y_619_);
lean_inc(v___y_627_);
v___x_638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_638_, 0, v___y_627_);
lean_ctor_set(v___x_638_, 1, v___y_619_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
lean_inc_ref(v___y_633_);
lean_inc(v___y_619_);
lean_inc(v___y_627_);
v___x_639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_639_, 0, v___y_627_);
lean_ctor_set(v___x_639_, 1, v___y_619_);
lean_ctor_set(v___x_639_, 2, v___y_633_);
lean_inc(v___y_627_);
v___x_640_ = l_Lean_Syntax_node1(v___y_627_, v___y_620_, v___x_639_);
lean_inc(v___y_627_);
v___x_641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_641_, 0, v___y_627_);
lean_ctor_set(v___x_641_, 1, v___y_632_);
v___x_642_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(v___y_627_);
v___x_643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_643_, 0, v___y_627_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_inc(v___y_627_);
v___x_644_ = l_Lean_Syntax_node2(v___y_627_, v___y_635_, v___x_643_, v___y_630_);
lean_inc(v___y_619_);
lean_inc(v___y_627_);
v___x_645_ = l_Lean_Syntax_node1(v___y_627_, v___y_619_, v___x_644_);
if (lean_obj_tag(v___y_621_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_val_646_ = lean_ctor_get(v___y_621_, 0);
lean_inc(v_val_646_);
lean_dec_ref(v___y_621_);
v___x_647_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_648_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_627_);
v___x_649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_627_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(v___y_627_);
v___x_651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_651_, 0, v___y_627_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_627_);
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_627_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_627_);
v___x_655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_655_, 0, v___y_627_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_inc(v___y_627_);
v___x_656_ = l_Lean_Syntax_node5(v___y_627_, v___x_647_, v___x_649_, v___x_651_, v___x_653_, v_val_646_, v___x_655_);
v___x_657_ = l_Array_mkArray1___redArg(v___x_656_);
v___y_586_ = v___y_619_;
v___y_587_ = v___y_622_;
v___y_588_ = v___y_623_;
v___y_589_ = v___x_645_;
v___y_590_ = v___x_638_;
v___y_591_ = v___y_624_;
v___y_592_ = v___y_625_;
v___y_593_ = v___x_640_;
v___y_594_ = v___y_626_;
v___y_595_ = v___y_627_;
v___y_596_ = v___x_641_;
v___y_597_ = v___y_628_;
v___y_598_ = v___y_629_;
v___y_599_ = v___y_631_;
v___y_600_ = v___y_633_;
v___y_601_ = v___y_634_;
v___y_602_ = v___x_657_;
goto v___jp_585_;
}
else
{
lean_object* v___x_658_; 
lean_dec(v___y_621_);
v___x_658_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_586_ = v___y_619_;
v___y_587_ = v___y_622_;
v___y_588_ = v___y_623_;
v___y_589_ = v___x_645_;
v___y_590_ = v___x_638_;
v___y_591_ = v___y_624_;
v___y_592_ = v___y_625_;
v___y_593_ = v___x_640_;
v___y_594_ = v___y_626_;
v___y_595_ = v___y_627_;
v___y_596_ = v___x_641_;
v___y_597_ = v___y_628_;
v___y_598_ = v___y_629_;
v___y_599_ = v___y_631_;
v___y_600_ = v___y_633_;
v___y_601_ = v___y_634_;
v___y_602_ = v___x_658_;
goto v___jp_585_;
}
}
v___jp_659_:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_inc_ref(v___y_674_);
v___x_678_ = l_Array_append___redArg(v___y_674_, v___y_677_);
lean_dec_ref(v___y_677_);
lean_inc(v___y_660_);
lean_inc(v___y_668_);
v___x_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_679_, 0, v___y_668_);
lean_ctor_set(v___x_679_, 1, v___y_660_);
lean_ctor_set(v___x_679_, 2, v___x_678_);
if (lean_obj_tag(v___y_665_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_val_680_ = lean_ctor_get(v___y_665_, 0);
lean_inc(v_val_680_);
lean_dec_ref(v___y_665_);
v___x_681_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_664_);
v___x_682_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_664_, v___x_681_);
v___x_683_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(v___y_668_);
v___x_684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_668_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
lean_inc_ref(v___y_674_);
v___x_685_ = l_Array_append___redArg(v___y_674_, v_val_680_);
lean_dec(v_val_680_);
lean_inc(v___y_660_);
lean_inc(v___y_668_);
v___x_686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_686_, 0, v___y_668_);
lean_ctor_set(v___x_686_, 1, v___y_660_);
lean_ctor_set(v___x_686_, 2, v___x_685_);
v___x_687_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(v___y_668_);
v___x_688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_688_, 0, v___y_668_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
lean_inc(v___y_668_);
v___x_689_ = l_Lean_Syntax_node3(v___y_668_, v___x_682_, v___x_684_, v___x_686_, v___x_688_);
v___x_690_ = l_Array_mkArray1___redArg(v___x_689_);
v___y_619_ = v___y_660_;
v___y_620_ = v___y_661_;
v___y_621_ = v___y_662_;
v___y_622_ = v___y_663_;
v___y_623_ = v___y_664_;
v___y_624_ = v___x_679_;
v___y_625_ = v___y_666_;
v___y_626_ = v___y_667_;
v___y_627_ = v___y_668_;
v___y_628_ = v___y_669_;
v___y_629_ = v___y_670_;
v___y_630_ = v___y_671_;
v___y_631_ = v___y_673_;
v___y_632_ = v___y_672_;
v___y_633_ = v___y_674_;
v___y_634_ = v___y_675_;
v___y_635_ = v___y_676_;
v___y_636_ = v___x_690_;
goto v___jp_618_;
}
else
{
lean_object* v___x_691_; 
lean_dec(v___y_665_);
v___x_691_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_619_ = v___y_660_;
v___y_620_ = v___y_661_;
v___y_621_ = v___y_662_;
v___y_622_ = v___y_663_;
v___y_623_ = v___y_664_;
v___y_624_ = v___x_679_;
v___y_625_ = v___y_666_;
v___y_626_ = v___y_667_;
v___y_627_ = v___y_668_;
v___y_628_ = v___y_669_;
v___y_629_ = v___y_670_;
v___y_630_ = v___y_671_;
v___y_631_ = v___y_673_;
v___y_632_ = v___y_672_;
v___y_633_ = v___y_674_;
v___y_634_ = v___y_675_;
v___y_635_ = v___y_676_;
v___y_636_ = v___x_691_;
goto v___jp_618_;
}
}
v___jp_692_:
{
lean_object* v_quotContext_704_; lean_object* v_currMacroScope_705_; lean_object* v_ref_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_quotContext_704_ = lean_ctor_get(v___y_702_, 1);
lean_inc(v_quotContext_704_);
v_currMacroScope_705_ = lean_ctor_get(v___y_702_, 2);
lean_inc(v_currMacroScope_705_);
v_ref_706_ = lean_ctor_get(v___y_702_, 5);
lean_inc(v_ref_706_);
lean_dec_ref(v___y_702_);
v___x_707_ = lean_unsigned_to_nat(7u);
v___x_708_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_707_);
v___x_709_ = lean_unsigned_to_nat(9u);
v___x_710_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_709_);
lean_dec(v_stx_147_);
v___x_711_ = l_Lean_SourceInfo_fromRef(v_ref_706_, v___y_696_);
lean_dec(v_ref_706_);
v___x_712_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_713_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_714_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_715_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_697_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_717_; 
v_val_716_ = lean_ctor_get(v___y_697_, 0);
lean_inc(v_val_716_);
lean_dec_ref(v___y_697_);
v___x_717_ = l_Array_mkArray1___redArg(v_val_716_);
v___y_660_ = v___x_714_;
v___y_661_ = v___y_693_;
v___y_662_ = v___y_694_;
v___y_663_ = v_prio_701_;
v___y_664_ = v___y_698_;
v___y_665_ = v___y_699_;
v___y_666_ = v_currMacroScope_705_;
v___y_667_ = v___x_708_;
v___y_668_ = v___x_711_;
v___y_669_ = v_quotContext_704_;
v___y_670_ = v___x_713_;
v___y_671_ = v___y_695_;
v___y_672_ = v___x_712_;
v___y_673_ = v___y_703_;
v___y_674_ = v___x_715_;
v___y_675_ = v___x_710_;
v___y_676_ = v___y_700_;
v___y_677_ = v___x_717_;
goto v___jp_659_;
}
else
{
lean_object* v___x_718_; 
lean_dec(v___y_697_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_660_ = v___x_714_;
v___y_661_ = v___y_693_;
v___y_662_ = v___y_694_;
v___y_663_ = v_prio_701_;
v___y_664_ = v___y_698_;
v___y_665_ = v___y_699_;
v___y_666_ = v_currMacroScope_705_;
v___y_667_ = v___x_708_;
v___y_668_ = v___x_711_;
v___y_669_ = v_quotContext_704_;
v___y_670_ = v___x_713_;
v___y_671_ = v___y_695_;
v___y_672_ = v___x_712_;
v___y_673_ = v___y_703_;
v___y_674_ = v___x_715_;
v___y_675_ = v___x_710_;
v___y_676_ = v___y_700_;
v___y_677_ = v___x_718_;
goto v___jp_659_;
}
}
v___jp_719_:
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = lean_unsigned_to_nat(6u);
v___x_733_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_732_);
v___x_734_ = l_Lean_Syntax_isNone(v___x_733_);
if (v___x_734_ == 0)
{
uint8_t v___x_735_; 
lean_inc(v___x_733_);
v___x_735_ = l_Lean_Syntax_matchesNull(v___x_733_, v___y_723_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_dec(v___x_733_);
lean_dec_ref(v___y_730_);
lean_dec(v_name_729_);
lean_dec(v___y_728_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_722_);
lean_dec(v___y_720_);
lean_dec(v_stx_147_);
v___x_736_ = l_Lean_Macro_throwUnsupported___redArg(v___y_731_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = l_Lean_Syntax_getArg(v___x_733_, v___x_425_);
lean_dec(v___x_733_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_737_);
v___x_739_ = l_Lean_Syntax_isOfKind(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v___x_737_);
lean_dec_ref(v___y_730_);
lean_dec(v_name_729_);
lean_dec(v___y_728_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_722_);
lean_dec(v___y_720_);
lean_dec(v_stx_147_);
v___x_740_ = l_Lean_Macro_throwUnsupported___redArg(v___y_731_);
return v___x_740_;
}
else
{
lean_object* v_prio_741_; lean_object* v___x_742_; 
v_prio_741_ = l_Lean_Syntax_getArg(v___x_737_, v___y_727_);
lean_dec(v___x_737_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_prio_741_);
v___y_693_ = v___y_720_;
v___y_694_ = v_name_729_;
v___y_695_ = v___y_722_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_725_;
v___y_698_ = v___y_724_;
v___y_699_ = v___y_726_;
v___y_700_ = v___y_728_;
v_prio_701_ = v___x_742_;
v___y_702_ = v___y_730_;
v___y_703_ = v___y_731_;
goto v___jp_692_;
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec(v___x_733_);
v___x_743_ = lean_box(0);
v___y_693_ = v___y_720_;
v___y_694_ = v_name_729_;
v___y_695_ = v___y_722_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_725_;
v___y_698_ = v___y_724_;
v___y_699_ = v___y_726_;
v___y_700_ = v___y_728_;
v_prio_701_ = v___x_743_;
v___y_702_ = v___y_730_;
v___y_703_ = v___y_731_;
goto v___jp_692_;
}
}
v___jp_744_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_inc_ref(v___y_760_);
v___x_765_ = l_Array_append___redArg(v___y_760_, v___y_764_);
lean_dec_ref(v___y_764_);
lean_inc(v___y_758_);
lean_inc(v___y_757_);
v___x_766_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_766_, 0, v___y_757_);
lean_ctor_set(v___x_766_, 1, v___y_758_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
if (lean_obj_tag(v___y_762_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_val_767_ = lean_ctor_get(v___y_762_, 0);
lean_inc(v_val_767_);
lean_dec_ref(v___y_762_);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_769_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_757_);
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_757_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(v___y_757_);
v___x_772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_772_, 0, v___y_757_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_757_);
v___x_774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_757_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_757_);
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v___y_757_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
lean_inc(v___y_757_);
v___x_777_ = l_Lean_Syntax_node5(v___y_757_, v___x_768_, v___x_770_, v___x_772_, v___x_774_, v_val_767_, v___x_776_);
v___x_778_ = l_Array_mkArray1___redArg(v___x_777_);
v___y_249_ = v___y_745_;
v___y_250_ = v___x_766_;
v___y_251_ = v___y_746_;
v___y_252_ = v___y_747_;
v___y_253_ = v___y_748_;
v___y_254_ = v___y_749_;
v___y_255_ = v___y_750_;
v___y_256_ = v___y_751_;
v___y_257_ = v___y_752_;
v___y_258_ = v___y_753_;
v___y_259_ = v___y_754_;
v___y_260_ = v___y_755_;
v___y_261_ = v___y_757_;
v___y_262_ = v___y_758_;
v___y_263_ = v___y_756_;
v___y_264_ = v___y_759_;
v___y_265_ = v___y_760_;
v___y_266_ = v___y_761_;
v___y_267_ = v___y_763_;
v___y_268_ = v___x_778_;
goto v___jp_248_;
}
else
{
lean_object* v___x_779_; 
lean_dec(v___y_762_);
v___x_779_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_249_ = v___y_745_;
v___y_250_ = v___x_766_;
v___y_251_ = v___y_746_;
v___y_252_ = v___y_747_;
v___y_253_ = v___y_748_;
v___y_254_ = v___y_749_;
v___y_255_ = v___y_750_;
v___y_256_ = v___y_751_;
v___y_257_ = v___y_752_;
v___y_258_ = v___y_753_;
v___y_259_ = v___y_754_;
v___y_260_ = v___y_755_;
v___y_261_ = v___y_757_;
v___y_262_ = v___y_758_;
v___y_263_ = v___y_756_;
v___y_264_ = v___y_759_;
v___y_265_ = v___y_760_;
v___y_266_ = v___y_761_;
v___y_267_ = v___y_763_;
v___y_268_ = v___x_779_;
goto v___jp_248_;
}
}
v___jp_780_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_inc_ref(v___y_796_);
v___x_800_ = l_Array_append___redArg(v___y_796_, v___y_799_);
lean_dec_ref(v___y_799_);
lean_inc(v___y_794_);
lean_inc(v___y_793_);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v___y_793_);
lean_ctor_set(v___x_801_, 1, v___y_794_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_794_);
lean_inc(v___y_793_);
v___x_802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_802_, 0, v___y_793_);
lean_ctor_set(v___x_802_, 1, v___y_794_);
lean_ctor_set(v___x_802_, 2, v___y_796_);
lean_inc(v___y_793_);
v___x_803_ = l_Lean_Syntax_node1(v___y_793_, v___y_782_, v___x_802_);
lean_inc(v___y_793_);
v___x_804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_804_, 0, v___y_793_);
lean_ctor_set(v___x_804_, 1, v___y_798_);
v___x_805_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(v___y_793_);
v___x_806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_806_, 0, v___y_793_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
lean_inc_ref(v___x_806_);
lean_inc(v___y_784_);
lean_inc(v___y_793_);
v___x_807_ = l_Lean_Syntax_node2(v___y_793_, v___y_784_, v___x_806_, v___y_781_);
lean_inc(v___y_794_);
lean_inc(v___y_793_);
v___x_808_ = l_Lean_Syntax_node1(v___y_793_, v___y_794_, v___x_807_);
if (lean_obj_tag(v___y_791_) == 1)
{
lean_object* v_val_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_val_809_ = lean_ctor_get(v___y_791_, 0);
lean_inc(v_val_809_);
lean_dec_ref(v___y_791_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_811_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_793_);
v___x_812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_812_, 0, v___y_793_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(v___y_793_);
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v___y_793_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_793_);
v___x_816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_816_, 0, v___y_793_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_793_);
v___x_818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_818_, 0, v___y_793_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
lean_inc(v___y_793_);
v___x_819_ = l_Lean_Syntax_node5(v___y_793_, v___x_810_, v___x_812_, v___x_814_, v___x_816_, v_val_809_, v___x_818_);
v___x_820_ = l_Array_mkArray1___redArg(v___x_819_);
v___y_745_ = v___x_803_;
v___y_746_ = v___y_783_;
v___y_747_ = v___y_784_;
v___y_748_ = v___y_785_;
v___y_749_ = v___y_786_;
v___y_750_ = v___y_787_;
v___y_751_ = v___y_788_;
v___y_752_ = v___x_806_;
v___y_753_ = v___y_789_;
v___y_754_ = v___y_790_;
v___y_755_ = v___x_801_;
v___y_756_ = v___y_792_;
v___y_757_ = v___y_793_;
v___y_758_ = v___y_794_;
v___y_759_ = v___y_795_;
v___y_760_ = v___y_796_;
v___y_761_ = v___x_808_;
v___y_762_ = v___y_797_;
v___y_763_ = v___x_804_;
v___y_764_ = v___x_820_;
goto v___jp_744_;
}
else
{
lean_object* v___x_821_; 
lean_dec(v___y_791_);
v___x_821_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_745_ = v___x_803_;
v___y_746_ = v___y_783_;
v___y_747_ = v___y_784_;
v___y_748_ = v___y_785_;
v___y_749_ = v___y_786_;
v___y_750_ = v___y_787_;
v___y_751_ = v___y_788_;
v___y_752_ = v___x_806_;
v___y_753_ = v___y_789_;
v___y_754_ = v___y_790_;
v___y_755_ = v___x_801_;
v___y_756_ = v___y_792_;
v___y_757_ = v___y_793_;
v___y_758_ = v___y_794_;
v___y_759_ = v___y_795_;
v___y_760_ = v___y_796_;
v___y_761_ = v___x_808_;
v___y_762_ = v___y_797_;
v___y_763_ = v___x_804_;
v___y_764_ = v___x_821_;
goto v___jp_744_;
}
}
v___jp_822_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_inc_ref(v___y_838_);
v___x_842_ = l_Array_append___redArg(v___y_838_, v___y_841_);
lean_dec_ref(v___y_841_);
lean_inc(v___y_836_);
lean_inc(v___y_835_);
v___x_843_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_843_, 0, v___y_835_);
lean_ctor_set(v___x_843_, 1, v___y_836_);
lean_ctor_set(v___x_843_, 2, v___x_842_);
if (lean_obj_tag(v___y_831_) == 1)
{
lean_object* v_val_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_val_844_ = lean_ctor_get(v___y_831_, 0);
lean_inc(v_val_844_);
lean_dec_ref(v___y_831_);
v___x_845_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_827_);
v___x_846_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_827_, v___x_845_);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(v___y_835_);
v___x_848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_848_, 0, v___y_835_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
lean_inc_ref(v___y_838_);
v___x_849_ = l_Array_append___redArg(v___y_838_, v_val_844_);
lean_dec(v_val_844_);
lean_inc(v___y_836_);
lean_inc(v___y_835_);
v___x_850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_850_, 0, v___y_835_);
lean_ctor_set(v___x_850_, 1, v___y_836_);
lean_ctor_set(v___x_850_, 2, v___x_849_);
v___x_851_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(v___y_835_);
v___x_852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_852_, 0, v___y_835_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
lean_inc(v___y_835_);
v___x_853_ = l_Lean_Syntax_node3(v___y_835_, v___x_846_, v___x_848_, v___x_850_, v___x_852_);
v___x_854_ = l_Array_mkArray1___redArg(v___x_853_);
v___y_781_ = v___y_823_;
v___y_782_ = v___y_824_;
v___y_783_ = v___y_825_;
v___y_784_ = v___y_826_;
v___y_785_ = v___y_827_;
v___y_786_ = v___y_828_;
v___y_787_ = v___y_829_;
v___y_788_ = v___y_830_;
v___y_789_ = v___y_832_;
v___y_790_ = v___y_833_;
v___y_791_ = v___y_834_;
v___y_792_ = v___x_843_;
v___y_793_ = v___y_835_;
v___y_794_ = v___y_836_;
v___y_795_ = v___y_837_;
v___y_796_ = v___y_838_;
v___y_797_ = v___y_840_;
v___y_798_ = v___y_839_;
v___y_799_ = v___x_854_;
goto v___jp_780_;
}
else
{
lean_object* v___x_855_; 
lean_dec(v___y_831_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_781_ = v___y_823_;
v___y_782_ = v___y_824_;
v___y_783_ = v___y_825_;
v___y_784_ = v___y_826_;
v___y_785_ = v___y_827_;
v___y_786_ = v___y_828_;
v___y_787_ = v___y_829_;
v___y_788_ = v___y_830_;
v___y_789_ = v___y_832_;
v___y_790_ = v___y_833_;
v___y_791_ = v___y_834_;
v___y_792_ = v___x_843_;
v___y_793_ = v___y_835_;
v___y_794_ = v___y_836_;
v___y_795_ = v___y_837_;
v___y_796_ = v___y_838_;
v___y_797_ = v___y_840_;
v___y_798_ = v___y_839_;
v___y_799_ = v___x_855_;
goto v___jp_780_;
}
}
v___jp_856_:
{
lean_object* v___x_869_; 
lean_inc_ref(v___y_867_);
lean_inc(v___y_857_);
v___x_869_ = l_Lean_evalPrec(v___y_857_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v_quotContext_872_; lean_object* v_currMacroScope_873_; lean_object* v_ref_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
v_a_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_a_871_);
lean_dec_ref(v___x_869_);
v_quotContext_872_ = lean_ctor_get(v___y_867_, 1);
lean_inc(v_quotContext_872_);
v_currMacroScope_873_ = lean_ctor_get(v___y_867_, 2);
lean_inc(v_currMacroScope_873_);
v_ref_874_ = lean_ctor_get(v___y_867_, 5);
lean_inc(v_ref_874_);
lean_dec_ref(v___y_867_);
v___x_875_ = lean_unsigned_to_nat(7u);
v___x_876_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_875_);
v___x_877_ = lean_unsigned_to_nat(9u);
v___x_878_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_877_);
lean_dec(v_stx_147_);
v___x_879_ = lean_nat_add(v_a_870_, v___y_864_);
lean_dec(v_a_870_);
v___x_880_ = l_Nat_reprFast(v___x_879_);
v___x_881_ = lean_box(2);
v___x_882_ = l_Lean_Syntax_mkNumLit(v___x_880_, v___x_881_);
v___x_883_ = l_Lean_SourceInfo_fromRef(v_ref_874_, v___y_860_);
lean_dec(v_ref_874_);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_885_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_886_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_887_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_861_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_889_; 
v_val_888_ = lean_ctor_get(v___y_861_, 0);
lean_inc(v_val_888_);
lean_dec_ref(v___y_861_);
v___x_889_ = l_Array_mkArray1___redArg(v_val_888_);
v___y_823_ = v___y_857_;
v___y_824_ = v___y_858_;
v___y_825_ = v_currMacroScope_873_;
v___y_826_ = v___y_863_;
v___y_827_ = v___y_862_;
v___y_828_ = v___x_876_;
v___y_829_ = v___x_885_;
v___y_830_ = v___x_878_;
v___y_831_ = v___y_865_;
v___y_832_ = v___x_882_;
v___y_833_ = v_quotContext_872_;
v___y_834_ = v___y_859_;
v___y_835_ = v___x_883_;
v___y_836_ = v___x_886_;
v___y_837_ = v_a_871_;
v___y_838_ = v___x_887_;
v___y_839_ = v___x_884_;
v___y_840_ = v_prio_866_;
v___y_841_ = v___x_889_;
goto v___jp_822_;
}
else
{
lean_object* v___x_890_; 
lean_dec(v___y_861_);
v___x_890_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_823_ = v___y_857_;
v___y_824_ = v___y_858_;
v___y_825_ = v_currMacroScope_873_;
v___y_826_ = v___y_863_;
v___y_827_ = v___y_862_;
v___y_828_ = v___x_876_;
v___y_829_ = v___x_885_;
v___y_830_ = v___x_878_;
v___y_831_ = v___y_865_;
v___y_832_ = v___x_882_;
v___y_833_ = v_quotContext_872_;
v___y_834_ = v___y_859_;
v___y_835_ = v___x_883_;
v___y_836_ = v___x_886_;
v___y_837_ = v_a_871_;
v___y_838_ = v___x_887_;
v___y_839_ = v___x_884_;
v___y_840_ = v_prio_866_;
v___y_841_ = v___x_890_;
goto v___jp_822_;
}
}
else
{
lean_object* v_a_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v___y_867_);
lean_dec(v_prio_866_);
lean_dec(v___y_865_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec(v___y_859_);
lean_dec(v___y_858_);
lean_dec(v___y_857_);
lean_dec(v_stx_147_);
v_a_891_ = lean_ctor_get(v___x_869_, 0);
v_a_892_ = lean_ctor_get(v___x_869_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_869_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_inc(v_a_891_);
lean_dec(v___x_869_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_891_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
v___jp_900_:
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_unsigned_to_nat(6u);
v___x_914_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_913_);
v___x_915_ = l_Lean_Syntax_isNone(v___x_914_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; 
lean_inc(v___x_914_);
v___x_916_ = l_Lean_Syntax_matchesNull(v___x_914_, v___y_904_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec(v___x_914_);
lean_dec_ref(v___y_911_);
lean_dec(v_name_910_);
lean_dec(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
lean_dec(v_stx_147_);
v___x_917_ = l_Lean_Macro_throwUnsupported___redArg(v___y_912_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = l_Lean_Syntax_getArg(v___x_914_, v___x_425_);
lean_dec(v___x_914_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_918_);
v___x_920_ = l_Lean_Syntax_isOfKind(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_dec(v___x_918_);
lean_dec_ref(v___y_911_);
lean_dec(v_name_910_);
lean_dec(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
lean_dec(v_stx_147_);
v___x_921_ = l_Lean_Macro_throwUnsupported___redArg(v___y_912_);
return v___x_921_;
}
else
{
lean_object* v_prio_922_; lean_object* v___x_923_; 
v_prio_922_ = l_Lean_Syntax_getArg(v___x_918_, v___y_909_);
lean_dec(v___x_918_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_prio_922_);
v___y_857_ = v___y_901_;
v___y_858_ = v___y_902_;
v___y_859_ = v_name_910_;
v___y_860_ = v___y_903_;
v___y_861_ = v___y_907_;
v___y_862_ = v___y_906_;
v___y_863_ = v___y_905_;
v___y_864_ = v___y_904_;
v___y_865_ = v___y_908_;
v_prio_866_ = v___x_923_;
v___y_867_ = v___y_911_;
v___y_868_ = v___y_912_;
goto v___jp_856_;
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_914_);
v___x_924_ = lean_box(0);
v___y_857_ = v___y_901_;
v___y_858_ = v___y_902_;
v___y_859_ = v_name_910_;
v___y_860_ = v___y_903_;
v___y_861_ = v___y_907_;
v___y_862_ = v___y_906_;
v___y_863_ = v___y_905_;
v___y_864_ = v___y_904_;
v___y_865_ = v___y_908_;
v_prio_866_ = v___x_924_;
v___y_867_ = v___y_911_;
v___y_868_ = v___y_912_;
goto v___jp_856_;
}
}
v___jp_925_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_inc_ref(v___y_940_);
v___x_946_ = l_Array_append___redArg(v___y_940_, v___y_945_);
lean_dec_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc(v___y_936_);
v___x_947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_947_, 0, v___y_936_);
lean_ctor_set(v___x_947_, 1, v___y_944_);
lean_ctor_set(v___x_947_, 2, v___x_946_);
if (lean_obj_tag(v___y_937_) == 1)
{
lean_object* v_val_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_val_948_ = lean_ctor_get(v___y_937_, 0);
lean_inc(v_val_948_);
lean_dec_ref(v___y_937_);
v___x_949_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_950_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_936_);
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___y_936_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(v___y_936_);
v___x_953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_953_, 0, v___y_936_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_936_);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___y_936_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_936_);
v___x_957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_957_, 0, v___y_936_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
lean_inc(v___y_936_);
v___x_958_ = l_Lean_Syntax_node5(v___y_936_, v___x_949_, v___x_951_, v___x_953_, v___x_955_, v_val_948_, v___x_957_);
v___x_959_ = l_Array_mkArray1___redArg(v___x_958_);
v___y_307_ = v___y_926_;
v___y_308_ = v___y_927_;
v___y_309_ = v___y_928_;
v___y_310_ = v___y_929_;
v___y_311_ = v___y_930_;
v___y_312_ = v___y_931_;
v___y_313_ = v___y_932_;
v___y_314_ = v___y_933_;
v___y_315_ = v___y_934_;
v___y_316_ = v___y_935_;
v___y_317_ = v___y_936_;
v___y_318_ = v___x_947_;
v___y_319_ = v___y_938_;
v___y_320_ = v___y_940_;
v___y_321_ = v___y_939_;
v___y_322_ = v___y_941_;
v___y_323_ = v___y_942_;
v___y_324_ = v___y_943_;
v___y_325_ = v___y_944_;
v___y_326_ = v___x_959_;
goto v___jp_306_;
}
else
{
lean_object* v___x_960_; 
lean_dec(v___y_937_);
v___x_960_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_307_ = v___y_926_;
v___y_308_ = v___y_927_;
v___y_309_ = v___y_928_;
v___y_310_ = v___y_929_;
v___y_311_ = v___y_930_;
v___y_312_ = v___y_931_;
v___y_313_ = v___y_932_;
v___y_314_ = v___y_933_;
v___y_315_ = v___y_934_;
v___y_316_ = v___y_935_;
v___y_317_ = v___y_936_;
v___y_318_ = v___x_947_;
v___y_319_ = v___y_938_;
v___y_320_ = v___y_940_;
v___y_321_ = v___y_939_;
v___y_322_ = v___y_941_;
v___y_323_ = v___y_942_;
v___y_324_ = v___y_943_;
v___y_325_ = v___y_944_;
v___y_326_ = v___x_960_;
goto v___jp_306_;
}
}
v___jp_961_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_inc_ref(v___y_976_);
v___x_981_ = l_Array_append___redArg(v___y_976_, v___y_980_);
lean_dec_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc(v___y_972_);
v___x_982_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_982_, 0, v___y_972_);
lean_ctor_set(v___x_982_, 1, v___y_979_);
lean_ctor_set(v___x_982_, 2, v___x_981_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_979_);
lean_inc(v___y_972_);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v___y_972_);
lean_ctor_set(v___x_983_, 1, v___y_979_);
lean_ctor_set(v___x_983_, 2, v___y_976_);
lean_inc(v___y_972_);
v___x_984_ = l_Lean_Syntax_node1(v___y_972_, v___y_963_, v___x_983_);
lean_inc(v___y_972_);
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___y_972_);
lean_ctor_set(v___x_985_, 1, v___y_971_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(v___y_972_);
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___y_972_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_inc_ref(v___x_987_);
lean_inc(v___y_966_);
lean_inc(v___y_972_);
v___x_988_ = l_Lean_Syntax_node2(v___y_972_, v___y_966_, v___x_987_, v___y_977_);
lean_inc(v___y_979_);
lean_inc(v___y_972_);
v___x_989_ = l_Lean_Syntax_node1(v___y_972_, v___y_979_, v___x_988_);
if (lean_obj_tag(v___y_973_) == 1)
{
lean_object* v_val_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_val_990_ = lean_ctor_get(v___y_973_, 0);
lean_inc(v_val_990_);
lean_dec_ref(v___y_973_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_992_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_972_);
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___y_972_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(v___y_972_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_972_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_972_);
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___y_972_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_972_);
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___y_972_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
lean_inc(v___y_972_);
v___x_1000_ = l_Lean_Syntax_node5(v___y_972_, v___x_991_, v___x_993_, v___x_995_, v___x_997_, v_val_990_, v___x_999_);
v___x_1001_ = l_Array_mkArray1___redArg(v___x_1000_);
v___y_926_ = v___y_962_;
v___y_927_ = v___y_964_;
v___y_928_ = v___x_985_;
v___y_929_ = v___y_965_;
v___y_930_ = v___y_966_;
v___y_931_ = v___y_967_;
v___y_932_ = v___y_968_;
v___y_933_ = v___x_984_;
v___y_934_ = v___y_969_;
v___y_935_ = v___y_970_;
v___y_936_ = v___y_972_;
v___y_937_ = v___y_974_;
v___y_938_ = v___x_989_;
v___y_939_ = v___y_975_;
v___y_940_ = v___y_976_;
v___y_941_ = v___x_982_;
v___y_942_ = v___x_987_;
v___y_943_ = v___y_978_;
v___y_944_ = v___y_979_;
v___y_945_ = v___x_1001_;
goto v___jp_925_;
}
else
{
lean_object* v___x_1002_; 
lean_dec(v___y_973_);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_926_ = v___y_962_;
v___y_927_ = v___y_964_;
v___y_928_ = v___x_985_;
v___y_929_ = v___y_965_;
v___y_930_ = v___y_966_;
v___y_931_ = v___y_967_;
v___y_932_ = v___y_968_;
v___y_933_ = v___x_984_;
v___y_934_ = v___y_969_;
v___y_935_ = v___y_970_;
v___y_936_ = v___y_972_;
v___y_937_ = v___y_974_;
v___y_938_ = v___x_989_;
v___y_939_ = v___y_975_;
v___y_940_ = v___y_976_;
v___y_941_ = v___x_982_;
v___y_942_ = v___x_987_;
v___y_943_ = v___y_978_;
v___y_944_ = v___y_979_;
v___y_945_ = v___x_1002_;
goto v___jp_925_;
}
}
v___jp_1003_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_inc_ref(v___y_1018_);
v___x_1023_ = l_Array_append___redArg(v___y_1018_, v___y_1022_);
lean_dec_ref(v___y_1022_);
lean_inc(v___y_1021_);
lean_inc(v___y_1014_);
v___x_1024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1024_, 0, v___y_1014_);
lean_ctor_set(v___x_1024_, 1, v___y_1021_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
if (lean_obj_tag(v___y_1011_) == 1)
{
lean_object* v_val_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_val_1025_ = lean_ctor_get(v___y_1011_, 0);
lean_inc(v_val_1025_);
lean_dec_ref(v___y_1011_);
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_1007_);
v___x_1027_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_1007_, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(v___y_1014_);
v___x_1029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___y_1014_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
lean_inc_ref(v___y_1018_);
v___x_1030_ = l_Array_append___redArg(v___y_1018_, v_val_1025_);
lean_dec(v_val_1025_);
lean_inc(v___y_1021_);
lean_inc(v___y_1014_);
v___x_1031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___y_1014_);
lean_ctor_set(v___x_1031_, 1, v___y_1021_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(v___y_1014_);
v___x_1033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___y_1014_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_inc(v___y_1014_);
v___x_1034_ = l_Lean_Syntax_node3(v___y_1014_, v___x_1027_, v___x_1029_, v___x_1031_, v___x_1033_);
v___x_1035_ = l_Array_mkArray1___redArg(v___x_1034_);
v___y_962_ = v___y_1004_;
v___y_963_ = v___y_1005_;
v___y_964_ = v___y_1006_;
v___y_965_ = v___y_1007_;
v___y_966_ = v___y_1008_;
v___y_967_ = v___y_1009_;
v___y_968_ = v___y_1010_;
v___y_969_ = v___x_1024_;
v___y_970_ = v___y_1012_;
v___y_971_ = v___y_1013_;
v___y_972_ = v___y_1014_;
v___y_973_ = v___y_1016_;
v___y_974_ = v___y_1015_;
v___y_975_ = v___y_1017_;
v___y_976_ = v___y_1018_;
v___y_977_ = v___y_1019_;
v___y_978_ = v___y_1020_;
v___y_979_ = v___y_1021_;
v___y_980_ = v___x_1035_;
goto v___jp_961_;
}
else
{
lean_object* v___x_1036_; 
lean_dec(v___y_1011_);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_962_ = v___y_1004_;
v___y_963_ = v___y_1005_;
v___y_964_ = v___y_1006_;
v___y_965_ = v___y_1007_;
v___y_966_ = v___y_1008_;
v___y_967_ = v___y_1009_;
v___y_968_ = v___y_1010_;
v___y_969_ = v___x_1024_;
v___y_970_ = v___y_1012_;
v___y_971_ = v___y_1013_;
v___y_972_ = v___y_1014_;
v___y_973_ = v___y_1016_;
v___y_974_ = v___y_1015_;
v___y_975_ = v___y_1017_;
v___y_976_ = v___y_1018_;
v___y_977_ = v___y_1019_;
v___y_978_ = v___y_1020_;
v___y_979_ = v___y_1021_;
v___y_980_ = v___x_1036_;
goto v___jp_961_;
}
}
v___jp_1037_:
{
lean_object* v___x_1050_; 
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1045_);
v___x_1050_ = l_Lean_evalPrec(v___y_1045_, v___y_1048_, v___y_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v_quotContext_1053_; lean_object* v_currMacroScope_1054_; lean_object* v_ref_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
v_a_1052_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_a_1052_);
lean_dec_ref(v___x_1050_);
v_quotContext_1053_ = lean_ctor_get(v___y_1048_, 1);
lean_inc(v_quotContext_1053_);
v_currMacroScope_1054_ = lean_ctor_get(v___y_1048_, 2);
lean_inc(v_currMacroScope_1054_);
v_ref_1055_ = lean_ctor_get(v___y_1048_, 5);
lean_inc(v_ref_1055_);
lean_dec_ref(v___y_1048_);
v___x_1056_ = lean_unsigned_to_nat(7u);
v___x_1057_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1056_);
v___x_1058_ = lean_unsigned_to_nat(9u);
v___x_1059_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1058_);
lean_dec(v_stx_147_);
v___x_1060_ = lean_nat_add(v_a_1051_, v___y_1042_);
lean_dec(v_a_1051_);
v___x_1061_ = l_Nat_reprFast(v___x_1060_);
v___x_1062_ = lean_box(2);
v___x_1063_ = l_Lean_Syntax_mkNumLit(v___x_1061_, v___x_1062_);
v___x_1064_ = l_Lean_SourceInfo_fromRef(v_ref_1055_, v___y_1044_);
lean_dec(v_ref_1055_);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_1068_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_1040_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1070_; 
v_val_1069_ = lean_ctor_get(v___y_1040_, 0);
lean_inc(v_val_1069_);
lean_dec_ref(v___y_1040_);
v___x_1070_ = l_Array_mkArray1___redArg(v_val_1069_);
v___y_1004_ = v___x_1066_;
v___y_1005_ = v___y_1038_;
v___y_1006_ = v___x_1059_;
v___y_1007_ = v___y_1041_;
v___y_1008_ = v___y_1043_;
v___y_1009_ = v___x_1057_;
v___y_1010_ = v___x_1063_;
v___y_1011_ = v___y_1046_;
v___y_1012_ = v_currMacroScope_1054_;
v___y_1013_ = v___x_1065_;
v___y_1014_ = v___x_1064_;
v___y_1015_ = v_prio_1047_;
v___y_1016_ = v___y_1039_;
v___y_1017_ = v_quotContext_1053_;
v___y_1018_ = v___x_1068_;
v___y_1019_ = v___y_1045_;
v___y_1020_ = v_a_1052_;
v___y_1021_ = v___x_1067_;
v___y_1022_ = v___x_1070_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1071_; 
lean_dec(v___y_1040_);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1004_ = v___x_1066_;
v___y_1005_ = v___y_1038_;
v___y_1006_ = v___x_1059_;
v___y_1007_ = v___y_1041_;
v___y_1008_ = v___y_1043_;
v___y_1009_ = v___x_1057_;
v___y_1010_ = v___x_1063_;
v___y_1011_ = v___y_1046_;
v___y_1012_ = v_currMacroScope_1054_;
v___y_1013_ = v___x_1065_;
v___y_1014_ = v___x_1064_;
v___y_1015_ = v_prio_1047_;
v___y_1016_ = v___y_1039_;
v___y_1017_ = v_quotContext_1053_;
v___y_1018_ = v___x_1068_;
v___y_1019_ = v___y_1045_;
v___y_1020_ = v_a_1052_;
v___y_1021_ = v___x_1067_;
v___y_1022_ = v___x_1071_;
goto v___jp_1003_;
}
}
else
{
lean_object* v_a_1072_; lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v___y_1048_);
lean_dec(v_prio_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec(v_stx_147_);
v_a_1072_ = lean_ctor_get(v___x_1050_, 0);
v_a_1073_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1050_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_inc(v_a_1072_);
lean_dec(v___x_1050_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1072_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
v___jp_1081_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = lean_unsigned_to_nat(6u);
v___x_1095_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1094_);
v___x_1096_ = l_Lean_Syntax_isNone(v___x_1095_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; 
lean_inc(v___x_1095_);
v___x_1097_ = l_Lean_Syntax_matchesNull(v___x_1095_, v___y_1083_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v___x_1095_);
lean_dec_ref(v___y_1092_);
lean_dec(v_name_1091_);
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1082_);
lean_dec(v_stx_147_);
v___x_1098_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1093_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = l_Lean_Syntax_getArg(v___x_1095_, v___x_425_);
lean_dec(v___x_1095_);
v___x_1100_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_1099_);
v___x_1101_ = l_Lean_Syntax_isOfKind(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v___x_1099_);
lean_dec_ref(v___y_1092_);
lean_dec(v_name_1091_);
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1082_);
lean_dec(v_stx_147_);
v___x_1102_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1093_);
return v___x_1102_;
}
else
{
lean_object* v_prio_1103_; lean_object* v___x_1104_; 
v_prio_1103_ = l_Lean_Syntax_getArg(v___x_1099_, v___y_1090_);
lean_dec(v___x_1099_);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_prio_1103_);
v___y_1038_ = v___y_1082_;
v___y_1039_ = v_name_1091_;
v___y_1040_ = v___y_1085_;
v___y_1041_ = v___y_1084_;
v___y_1042_ = v___y_1083_;
v___y_1043_ = v___y_1086_;
v___y_1044_ = v___y_1087_;
v___y_1045_ = v___y_1088_;
v___y_1046_ = v___y_1089_;
v_prio_1047_ = v___x_1104_;
v___y_1048_ = v___y_1092_;
v___y_1049_ = v___y_1093_;
goto v___jp_1037_;
}
}
}
else
{
lean_object* v___x_1105_; 
lean_dec(v___x_1095_);
v___x_1105_ = lean_box(0);
v___y_1038_ = v___y_1082_;
v___y_1039_ = v_name_1091_;
v___y_1040_ = v___y_1085_;
v___y_1041_ = v___y_1084_;
v___y_1042_ = v___y_1083_;
v___y_1043_ = v___y_1086_;
v___y_1044_ = v___y_1087_;
v___y_1045_ = v___y_1088_;
v___y_1046_ = v___y_1089_;
v_prio_1047_ = v___x_1105_;
v___y_1048_ = v___y_1092_;
v___y_1049_ = v___y_1093_;
goto v___jp_1037_;
}
}
v___jp_1106_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc_ref(v___y_1120_);
v___x_1127_ = l_Array_append___redArg(v___y_1120_, v___y_1126_);
lean_dec_ref(v___y_1126_);
lean_inc(v___y_1122_);
lean_inc(v___y_1111_);
v___x_1128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1128_, 0, v___y_1111_);
lean_ctor_set(v___x_1128_, 1, v___y_1122_);
lean_ctor_set(v___x_1128_, 2, v___x_1127_);
if (lean_obj_tag(v___y_1123_) == 1)
{
lean_object* v_val_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_val_1129_ = lean_ctor_get(v___y_1123_, 0);
lean_inc(v_val_1129_);
lean_dec_ref(v___y_1123_);
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_1131_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_1111_);
v___x_1132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___y_1111_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(v___y_1111_);
v___x_1134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1111_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_1111_);
v___x_1136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___y_1111_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_1111_);
v___x_1138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___y_1111_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
lean_inc(v___y_1111_);
v___x_1139_ = l_Lean_Syntax_node5(v___y_1111_, v___x_1130_, v___x_1132_, v___x_1134_, v___x_1136_, v_val_1129_, v___x_1138_);
v___x_1140_ = l_Array_mkArray1___redArg(v___x_1139_);
v___y_365_ = v___y_1107_;
v___y_366_ = v___y_1108_;
v___y_367_ = v___y_1109_;
v___y_368_ = v___y_1110_;
v___y_369_ = v___y_1111_;
v___y_370_ = v___y_1112_;
v___y_371_ = v___y_1113_;
v___y_372_ = v___y_1114_;
v___y_373_ = v___y_1115_;
v___y_374_ = v___y_1116_;
v___y_375_ = v___y_1117_;
v___y_376_ = v___y_1118_;
v___y_377_ = v___y_1120_;
v___y_378_ = v___y_1119_;
v___y_379_ = v___y_1121_;
v___y_380_ = v___y_1122_;
v___y_381_ = v___y_1124_;
v___y_382_ = v___x_1128_;
v___y_383_ = v___y_1125_;
v___y_384_ = v___x_1140_;
goto v___jp_364_;
}
else
{
lean_object* v___x_1141_; 
lean_dec(v___y_1123_);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_365_ = v___y_1107_;
v___y_366_ = v___y_1108_;
v___y_367_ = v___y_1109_;
v___y_368_ = v___y_1110_;
v___y_369_ = v___y_1111_;
v___y_370_ = v___y_1112_;
v___y_371_ = v___y_1113_;
v___y_372_ = v___y_1114_;
v___y_373_ = v___y_1115_;
v___y_374_ = v___y_1116_;
v___y_375_ = v___y_1117_;
v___y_376_ = v___y_1118_;
v___y_377_ = v___y_1120_;
v___y_378_ = v___y_1119_;
v___y_379_ = v___y_1121_;
v___y_380_ = v___y_1122_;
v___y_381_ = v___y_1124_;
v___y_382_ = v___x_1128_;
v___y_383_ = v___y_1125_;
v___y_384_ = v___x_1141_;
goto v___jp_364_;
}
}
v___jp_1142_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc_ref(v___y_1156_);
v___x_1162_ = l_Array_append___redArg(v___y_1156_, v___y_1161_);
lean_dec_ref(v___y_1161_);
lean_inc(v___y_1158_);
lean_inc(v___y_1147_);
v___x_1163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1163_, 0, v___y_1147_);
lean_ctor_set(v___x_1163_, 1, v___y_1158_);
lean_ctor_set(v___x_1163_, 2, v___x_1162_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1158_);
lean_inc(v___y_1147_);
v___x_1164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1164_, 0, v___y_1147_);
lean_ctor_set(v___x_1164_, 1, v___y_1158_);
lean_ctor_set(v___x_1164_, 2, v___y_1156_);
lean_inc(v___y_1147_);
v___x_1165_ = l_Lean_Syntax_node1(v___y_1147_, v___y_1144_, v___x_1164_);
lean_inc(v___y_1147_);
v___x_1166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___y_1147_);
lean_ctor_set(v___x_1166_, 1, v___y_1151_);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(v___y_1147_);
v___x_1168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___y_1147_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
lean_inc_ref(v___x_1168_);
lean_inc(v___y_1155_);
lean_inc(v___y_1147_);
v___x_1169_ = l_Lean_Syntax_node2(v___y_1147_, v___y_1155_, v___x_1168_, v___y_1145_);
lean_inc(v___y_1158_);
lean_inc(v___y_1147_);
v___x_1170_ = l_Lean_Syntax_node1(v___y_1147_, v___y_1158_, v___x_1169_);
if (lean_obj_tag(v___y_1143_) == 1)
{
lean_object* v_val_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_val_1171_ = lean_ctor_get(v___y_1143_, 0);
lean_inc(v_val_1171_);
lean_dec_ref(v___y_1143_);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(v___y_1147_);
v___x_1174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1147_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(v___y_1147_);
v___x_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___y_1147_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(v___y_1147_);
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___y_1147_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(v___y_1147_);
v___x_1180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___y_1147_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
lean_inc(v___y_1147_);
v___x_1181_ = l_Lean_Syntax_node5(v___y_1147_, v___x_1172_, v___x_1174_, v___x_1176_, v___x_1178_, v_val_1171_, v___x_1180_);
v___x_1182_ = l_Array_mkArray1___redArg(v___x_1181_);
v___y_1107_ = v___x_1170_;
v___y_1108_ = v___y_1146_;
v___y_1109_ = v___x_1166_;
v___y_1110_ = v___x_1165_;
v___y_1111_ = v___y_1147_;
v___y_1112_ = v___y_1148_;
v___y_1113_ = v___y_1149_;
v___y_1114_ = v___y_1150_;
v___y_1115_ = v___y_1152_;
v___y_1116_ = v___y_1153_;
v___y_1117_ = v___y_1154_;
v___y_1118_ = v___y_1155_;
v___y_1119_ = v___x_1168_;
v___y_1120_ = v___y_1156_;
v___y_1121_ = v___y_1157_;
v___y_1122_ = v___y_1158_;
v___y_1123_ = v___y_1160_;
v___y_1124_ = v___y_1159_;
v___y_1125_ = v___x_1163_;
v___y_1126_ = v___x_1182_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1183_; 
lean_dec(v___y_1143_);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1107_ = v___x_1170_;
v___y_1108_ = v___y_1146_;
v___y_1109_ = v___x_1166_;
v___y_1110_ = v___x_1165_;
v___y_1111_ = v___y_1147_;
v___y_1112_ = v___y_1148_;
v___y_1113_ = v___y_1149_;
v___y_1114_ = v___y_1150_;
v___y_1115_ = v___y_1152_;
v___y_1116_ = v___y_1153_;
v___y_1117_ = v___y_1154_;
v___y_1118_ = v___y_1155_;
v___y_1119_ = v___x_1168_;
v___y_1120_ = v___y_1156_;
v___y_1121_ = v___y_1157_;
v___y_1122_ = v___y_1158_;
v___y_1123_ = v___y_1160_;
v___y_1124_ = v___y_1159_;
v___y_1125_ = v___x_1163_;
v___y_1126_ = v___x_1183_;
goto v___jp_1106_;
}
}
v___jp_1184_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_inc_ref(v___y_1199_);
v___x_1204_ = l_Array_append___redArg(v___y_1199_, v___y_1203_);
lean_dec_ref(v___y_1203_);
lean_inc(v___y_1201_);
lean_inc(v___y_1189_);
v___x_1205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1205_, 0, v___y_1189_);
lean_ctor_set(v___x_1205_, 1, v___y_1201_);
lean_ctor_set(v___x_1205_, 2, v___x_1204_);
if (lean_obj_tag(v___y_1193_) == 1)
{
lean_object* v_val_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_val_1206_ = lean_ctor_get(v___y_1193_, 0);
lean_inc(v_val_1206_);
lean_dec_ref(v___y_1193_);
v___x_1207_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_1191_);
v___x_1208_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_1191_, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(v___y_1189_);
v___x_1210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___y_1189_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
lean_inc_ref(v___y_1199_);
v___x_1211_ = l_Array_append___redArg(v___y_1199_, v_val_1206_);
lean_dec(v_val_1206_);
lean_inc(v___y_1201_);
lean_inc(v___y_1189_);
v___x_1212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1212_, 0, v___y_1189_);
lean_ctor_set(v___x_1212_, 1, v___y_1201_);
lean_ctor_set(v___x_1212_, 2, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(v___y_1189_);
v___x_1214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___y_1189_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
lean_inc(v___y_1189_);
v___x_1215_ = l_Lean_Syntax_node3(v___y_1189_, v___x_1208_, v___x_1210_, v___x_1212_, v___x_1214_);
v___x_1216_ = l_Array_mkArray1___redArg(v___x_1215_);
v___y_1143_ = v___y_1185_;
v___y_1144_ = v___y_1186_;
v___y_1145_ = v___y_1187_;
v___y_1146_ = v___y_1188_;
v___y_1147_ = v___y_1189_;
v___y_1148_ = v___y_1190_;
v___y_1149_ = v___y_1191_;
v___y_1150_ = v___y_1192_;
v___y_1151_ = v___y_1194_;
v___y_1152_ = v___y_1195_;
v___y_1153_ = v___y_1196_;
v___y_1154_ = v___y_1197_;
v___y_1155_ = v___y_1198_;
v___y_1156_ = v___y_1199_;
v___y_1157_ = v___y_1200_;
v___y_1158_ = v___y_1201_;
v___y_1159_ = v___x_1205_;
v___y_1160_ = v___y_1202_;
v___y_1161_ = v___x_1216_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1217_; 
lean_dec(v___y_1193_);
v___x_1217_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1143_ = v___y_1185_;
v___y_1144_ = v___y_1186_;
v___y_1145_ = v___y_1187_;
v___y_1146_ = v___y_1188_;
v___y_1147_ = v___y_1189_;
v___y_1148_ = v___y_1190_;
v___y_1149_ = v___y_1191_;
v___y_1150_ = v___y_1192_;
v___y_1151_ = v___y_1194_;
v___y_1152_ = v___y_1195_;
v___y_1153_ = v___y_1196_;
v___y_1154_ = v___y_1197_;
v___y_1155_ = v___y_1198_;
v___y_1156_ = v___y_1199_;
v___y_1157_ = v___y_1200_;
v___y_1158_ = v___y_1201_;
v___y_1159_ = v___x_1205_;
v___y_1160_ = v___y_1202_;
v___y_1161_ = v___x_1217_;
goto v___jp_1142_;
}
}
v___jp_1218_:
{
lean_object* v___x_1230_; 
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1221_);
v___x_1230_ = l_Lean_evalPrec(v___y_1221_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v_a_1232_; lean_object* v_quotContext_1233_; lean_object* v_currMacroScope_1234_; lean_object* v_ref_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
v_a_1232_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1230_);
v_quotContext_1233_ = lean_ctor_get(v___y_1228_, 1);
lean_inc(v_quotContext_1233_);
v_currMacroScope_1234_ = lean_ctor_get(v___y_1228_, 2);
lean_inc(v_currMacroScope_1234_);
v_ref_1235_ = lean_ctor_get(v___y_1228_, 5);
lean_inc(v_ref_1235_);
lean_dec_ref(v___y_1228_);
v___x_1236_ = lean_unsigned_to_nat(7u);
v___x_1237_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1236_);
v___x_1238_ = lean_unsigned_to_nat(9u);
v___x_1239_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1238_);
lean_dec(v_stx_147_);
v___x_1240_ = lean_nat_add(v_a_1231_, v___y_1225_);
lean_dec(v_a_1231_);
v___x_1241_ = l_Nat_reprFast(v___x_1240_);
v___x_1242_ = lean_box(2);
v___x_1243_ = l_Lean_Syntax_mkNumLit(v___x_1241_, v___x_1242_);
v___x_1244_ = 0;
v___x_1245_ = l_Lean_SourceInfo_fromRef(v_ref_1235_, v___x_1244_);
lean_dec(v_ref_1235_);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_1247_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_1249_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_1223_) == 1)
{
lean_object* v_val_1250_; lean_object* v___x_1251_; 
v_val_1250_ = lean_ctor_get(v___y_1223_, 0);
lean_inc(v_val_1250_);
lean_dec_ref(v___y_1223_);
v___x_1251_ = l_Array_mkArray1___redArg(v_val_1250_);
v___y_1185_ = v___y_1220_;
v___y_1186_ = v___y_1219_;
v___y_1187_ = v___y_1221_;
v___y_1188_ = v___x_1247_;
v___y_1189_ = v___x_1245_;
v___y_1190_ = v_currMacroScope_1234_;
v___y_1191_ = v___y_1224_;
v___y_1192_ = v___x_1243_;
v___y_1193_ = v___y_1226_;
v___y_1194_ = v___x_1246_;
v___y_1195_ = v_a_1232_;
v___y_1196_ = v___x_1239_;
v___y_1197_ = v___x_1237_;
v___y_1198_ = v___y_1222_;
v___y_1199_ = v___x_1249_;
v___y_1200_ = v_quotContext_1233_;
v___y_1201_ = v___x_1248_;
v___y_1202_ = v_prio_1227_;
v___y_1203_ = v___x_1251_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1252_; 
lean_dec(v___y_1223_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1185_ = v___y_1220_;
v___y_1186_ = v___y_1219_;
v___y_1187_ = v___y_1221_;
v___y_1188_ = v___x_1247_;
v___y_1189_ = v___x_1245_;
v___y_1190_ = v_currMacroScope_1234_;
v___y_1191_ = v___y_1224_;
v___y_1192_ = v___x_1243_;
v___y_1193_ = v___y_1226_;
v___y_1194_ = v___x_1246_;
v___y_1195_ = v_a_1232_;
v___y_1196_ = v___x_1239_;
v___y_1197_ = v___x_1237_;
v___y_1198_ = v___y_1222_;
v___y_1199_ = v___x_1249_;
v___y_1200_ = v_quotContext_1233_;
v___y_1201_ = v___x_1248_;
v___y_1202_ = v_prio_1227_;
v___y_1203_ = v___x_1252_;
goto v___jp_1184_;
}
}
else
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v___y_1228_);
lean_dec(v_prio_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v_stx_147_);
v_a_1253_ = lean_ctor_get(v___x_1230_, 0);
v_a_1254_ = lean_ctor_get(v___x_1230_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1230_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_inc(v_a_1253_);
lean_dec(v___x_1230_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
v___jp_1262_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1274_ = lean_unsigned_to_nat(6u);
v___x_1275_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1274_);
v___x_1276_ = l_Lean_Syntax_isNone(v___x_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
lean_inc(v___x_1275_);
v___x_1277_ = l_Lean_Syntax_matchesNull(v___x_1275_, v___y_1266_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_dec(v___x_1275_);
lean_dec_ref(v___y_1272_);
lean_dec(v_name_1271_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v_stx_147_);
v___x_1278_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1273_);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = l_Lean_Syntax_getArg(v___x_1275_, v___x_425_);
lean_dec(v___x_1275_);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_1279_);
v___x_1281_ = l_Lean_Syntax_isOfKind(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v___x_1279_);
lean_dec_ref(v___y_1272_);
lean_dec(v_name_1271_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v_stx_147_);
v___x_1282_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1273_);
return v___x_1282_;
}
else
{
lean_object* v_prio_1283_; lean_object* v___x_1284_; 
v_prio_1283_ = l_Lean_Syntax_getArg(v___x_1279_, v___y_1270_);
lean_dec(v___x_1279_);
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_prio_1283_);
v___y_1219_ = v___y_1264_;
v___y_1220_ = v_name_1271_;
v___y_1221_ = v___y_1263_;
v___y_1222_ = v___y_1265_;
v___y_1223_ = v___y_1268_;
v___y_1224_ = v___y_1267_;
v___y_1225_ = v___y_1266_;
v___y_1226_ = v___y_1269_;
v_prio_1227_ = v___x_1284_;
v___y_1228_ = v___y_1272_;
v___y_1229_ = v___y_1273_;
goto v___jp_1218_;
}
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v___x_1275_);
v___x_1285_ = lean_box(0);
v___y_1219_ = v___y_1264_;
v___y_1220_ = v_name_1271_;
v___y_1221_ = v___y_1263_;
v___y_1222_ = v___y_1265_;
v___y_1223_ = v___y_1268_;
v___y_1224_ = v___y_1267_;
v___y_1225_ = v___y_1266_;
v___y_1226_ = v___y_1269_;
v_prio_1227_ = v___x_1285_;
v___y_1228_ = v___y_1272_;
v___y_1229_ = v___y_1273_;
goto v___jp_1218_;
}
}
v___jp_1286_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1292_ = lean_unsigned_to_nat(2u);
v___x_1293_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37));
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39));
lean_inc(v___x_1293_);
v___x_1296_ = l_Lean_Syntax_isOfKind(v___x_1293_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_dec(v___x_1293_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1297_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = l_Lean_Syntax_getArg(v___x_1293_, v___x_425_);
lean_dec(v___x_1293_);
v___x_1299_ = l_Lean_Syntax_matchesNull(v___x_1298_, v___x_425_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1300_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1301_ = lean_unsigned_to_nat(3u);
v___x_1302_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41));
lean_inc(v___x_1302_);
v___x_1304_ = l_Lean_Syntax_isOfKind(v___x_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43));
lean_inc(v___x_1302_);
v___x_1306_ = l_Lean_Syntax_isOfKind(v___x_1302_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45));
lean_inc(v___x_1302_);
v___x_1308_ = l_Lean_Syntax_isOfKind(v___x_1302_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47));
lean_inc(v___x_1302_);
v___x_1310_ = l_Lean_Syntax_isOfKind(v___x_1302_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49));
v___x_1312_ = l_Lean_Syntax_isOfKind(v___x_1302_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1313_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1314_ = lean_unsigned_to_nat(4u);
v___x_1315_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1314_);
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1315_);
v___x_1317_ = l_Lean_Syntax_isOfKind(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec(v___x_1315_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1318_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1319_ = l_Lean_Syntax_getArg(v___x_1315_, v___y_1288_);
lean_dec(v___x_1315_);
v___x_1320_ = lean_unsigned_to_nat(5u);
v___x_1321_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1320_);
v___x_1322_ = l_Lean_Syntax_isNone(v___x_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; 
lean_inc(v___x_1321_);
v___x_1323_ = l_Lean_Syntax_matchesNull(v___x_1321_, v___y_1288_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v___x_1321_);
lean_dec(v___x_1319_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1324_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1325_ = l_Lean_Syntax_getArg(v___x_1321_, v___x_425_);
lean_dec(v___x_1321_);
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1325_);
v___x_1327_ = l_Lean_Syntax_isOfKind(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec(v___x_1325_);
lean_dec(v___x_1319_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1328_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1328_;
}
else
{
lean_object* v_name_1329_; lean_object* v___x_1330_; 
v_name_1329_ = l_Lean_Syntax_getArg(v___x_1325_, v___x_1301_);
lean_dec(v___x_1325_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_name_1329_);
v___y_561_ = v___x_1295_;
v___y_562_ = v___x_1316_;
v___y_563_ = v___y_1288_;
v___y_564_ = v___x_1294_;
v___y_565_ = v___y_1287_;
v___y_566_ = v___x_1310_;
v___y_567_ = v_attrs_x3f_1289_;
v___y_568_ = v___x_1319_;
v___y_569_ = v___x_1301_;
v_name_570_ = v___x_1330_;
v___y_571_ = v___y_1290_;
v___y_572_ = v___y_1291_;
goto v___jp_560_;
}
}
}
else
{
lean_object* v___x_1331_; 
lean_dec(v___x_1321_);
v___x_1331_ = lean_box(0);
v___y_561_ = v___x_1295_;
v___y_562_ = v___x_1316_;
v___y_563_ = v___y_1288_;
v___y_564_ = v___x_1294_;
v___y_565_ = v___y_1287_;
v___y_566_ = v___x_1310_;
v___y_567_ = v_attrs_x3f_1289_;
v___y_568_ = v___x_1319_;
v___y_569_ = v___x_1301_;
v_name_570_ = v___x_1331_;
v___y_571_ = v___y_1290_;
v___y_572_ = v___y_1291_;
goto v___jp_560_;
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
lean_dec(v___x_1302_);
v___x_1332_ = lean_unsigned_to_nat(4u);
v___x_1333_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1333_);
v___x_1335_ = l_Lean_Syntax_isOfKind(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec(v___x_1333_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1336_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1337_ = l_Lean_Syntax_getArg(v___x_1333_, v___y_1288_);
lean_dec(v___x_1333_);
v___x_1338_ = lean_unsigned_to_nat(5u);
v___x_1339_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1338_);
v___x_1340_ = l_Lean_Syntax_isNone(v___x_1339_);
if (v___x_1340_ == 0)
{
uint8_t v___x_1341_; 
lean_inc(v___x_1339_);
v___x_1341_ = l_Lean_Syntax_matchesNull(v___x_1339_, v___y_1288_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec(v___x_1339_);
lean_dec(v___x_1337_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1342_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = l_Lean_Syntax_getArg(v___x_1339_, v___x_425_);
lean_dec(v___x_1339_);
v___x_1344_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1343_);
v___x_1345_ = l_Lean_Syntax_isOfKind(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec(v___x_1343_);
lean_dec(v___x_1337_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1346_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1346_;
}
else
{
lean_object* v_name_1347_; lean_object* v___x_1348_; 
v_name_1347_ = l_Lean_Syntax_getArg(v___x_1343_, v___x_1301_);
lean_dec(v___x_1343_);
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v_name_1347_);
v___y_720_ = v___x_1295_;
v___y_721_ = v___x_1308_;
v___y_722_ = v___x_1337_;
v___y_723_ = v___y_1288_;
v___y_724_ = v___x_1294_;
v___y_725_ = v___y_1287_;
v___y_726_ = v_attrs_x3f_1289_;
v___y_727_ = v___x_1301_;
v___y_728_ = v___x_1334_;
v_name_729_ = v___x_1348_;
v___y_730_ = v___y_1290_;
v___y_731_ = v___y_1291_;
goto v___jp_719_;
}
}
}
else
{
lean_object* v___x_1349_; 
lean_dec(v___x_1339_);
v___x_1349_ = lean_box(0);
v___y_720_ = v___x_1295_;
v___y_721_ = v___x_1308_;
v___y_722_ = v___x_1337_;
v___y_723_ = v___y_1288_;
v___y_724_ = v___x_1294_;
v___y_725_ = v___y_1287_;
v___y_726_ = v_attrs_x3f_1289_;
v___y_727_ = v___x_1301_;
v___y_728_ = v___x_1334_;
v_name_729_ = v___x_1349_;
v___y_730_ = v___y_1290_;
v___y_731_ = v___y_1291_;
goto v___jp_719_;
}
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
lean_dec(v___x_1302_);
v___x_1350_ = lean_unsigned_to_nat(4u);
v___x_1351_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1351_);
v___x_1353_ = l_Lean_Syntax_isOfKind(v___x_1351_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec(v___x_1351_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1354_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1355_ = l_Lean_Syntax_getArg(v___x_1351_, v___y_1288_);
lean_dec(v___x_1351_);
v___x_1356_ = lean_unsigned_to_nat(5u);
v___x_1357_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_isNone(v___x_1357_);
if (v___x_1358_ == 0)
{
uint8_t v___x_1359_; 
lean_inc(v___x_1357_);
v___x_1359_ = l_Lean_Syntax_matchesNull(v___x_1357_, v___y_1288_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_dec(v___x_1357_);
lean_dec(v___x_1355_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1360_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = l_Lean_Syntax_getArg(v___x_1357_, v___x_425_);
lean_dec(v___x_1357_);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1361_);
v___x_1363_ = l_Lean_Syntax_isOfKind(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_dec(v___x_1361_);
lean_dec(v___x_1355_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1364_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1364_;
}
else
{
lean_object* v_name_1365_; lean_object* v___x_1366_; 
v_name_1365_ = l_Lean_Syntax_getArg(v___x_1361_, v___x_1301_);
lean_dec(v___x_1361_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_name_1365_);
v___y_901_ = v___x_1355_;
v___y_902_ = v___x_1295_;
v___y_903_ = v___x_1306_;
v___y_904_ = v___y_1288_;
v___y_905_ = v___x_1352_;
v___y_906_ = v___x_1294_;
v___y_907_ = v___y_1287_;
v___y_908_ = v_attrs_x3f_1289_;
v___y_909_ = v___x_1301_;
v_name_910_ = v___x_1366_;
v___y_911_ = v___y_1290_;
v___y_912_ = v___y_1291_;
goto v___jp_900_;
}
}
}
else
{
lean_object* v___x_1367_; 
lean_dec(v___x_1357_);
v___x_1367_ = lean_box(0);
v___y_901_ = v___x_1355_;
v___y_902_ = v___x_1295_;
v___y_903_ = v___x_1306_;
v___y_904_ = v___y_1288_;
v___y_905_ = v___x_1352_;
v___y_906_ = v___x_1294_;
v___y_907_ = v___y_1287_;
v___y_908_ = v_attrs_x3f_1289_;
v___y_909_ = v___x_1301_;
v_name_910_ = v___x_1367_;
v___y_911_ = v___y_1290_;
v___y_912_ = v___y_1291_;
goto v___jp_900_;
}
}
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
lean_dec(v___x_1302_);
v___x_1368_ = lean_unsigned_to_nat(4u);
v___x_1369_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1369_);
v___x_1371_ = l_Lean_Syntax_isOfKind(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v___x_1369_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1372_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1373_ = l_Lean_Syntax_getArg(v___x_1369_, v___y_1288_);
lean_dec(v___x_1369_);
v___x_1374_ = lean_unsigned_to_nat(5u);
v___x_1375_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1374_);
v___x_1376_ = l_Lean_Syntax_isNone(v___x_1375_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
lean_inc(v___x_1375_);
v___x_1377_ = l_Lean_Syntax_matchesNull(v___x_1375_, v___y_1288_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec(v___x_1375_);
lean_dec(v___x_1373_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1378_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1379_ = l_Lean_Syntax_getArg(v___x_1375_, v___x_425_);
lean_dec(v___x_1375_);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1379_);
v___x_1381_ = l_Lean_Syntax_isOfKind(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec(v___x_1379_);
lean_dec(v___x_1373_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1382_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1382_;
}
else
{
lean_object* v_name_1383_; lean_object* v___x_1384_; 
v_name_1383_ = l_Lean_Syntax_getArg(v___x_1379_, v___x_1301_);
lean_dec(v___x_1379_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_name_1383_);
v___y_1082_ = v___x_1295_;
v___y_1083_ = v___y_1288_;
v___y_1084_ = v___x_1294_;
v___y_1085_ = v___y_1287_;
v___y_1086_ = v___x_1370_;
v___y_1087_ = v___x_1304_;
v___y_1088_ = v___x_1373_;
v___y_1089_ = v_attrs_x3f_1289_;
v___y_1090_ = v___x_1301_;
v_name_1091_ = v___x_1384_;
v___y_1092_ = v___y_1290_;
v___y_1093_ = v___y_1291_;
goto v___jp_1081_;
}
}
}
else
{
lean_object* v___x_1385_; 
lean_dec(v___x_1375_);
v___x_1385_ = lean_box(0);
v___y_1082_ = v___x_1295_;
v___y_1083_ = v___y_1288_;
v___y_1084_ = v___x_1294_;
v___y_1085_ = v___y_1287_;
v___y_1086_ = v___x_1370_;
v___y_1087_ = v___x_1304_;
v___y_1088_ = v___x_1373_;
v___y_1089_ = v_attrs_x3f_1289_;
v___y_1090_ = v___x_1301_;
v_name_1091_ = v___x_1385_;
v___y_1092_ = v___y_1290_;
v___y_1093_ = v___y_1291_;
goto v___jp_1081_;
}
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
lean_dec(v___x_1302_);
v___x_1386_ = lean_unsigned_to_nat(4u);
v___x_1387_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1387_);
v___x_1389_ = l_Lean_Syntax_isOfKind(v___x_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v___x_1387_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1390_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1391_ = l_Lean_Syntax_getArg(v___x_1387_, v___y_1288_);
lean_dec(v___x_1387_);
v___x_1392_ = lean_unsigned_to_nat(5u);
v___x_1393_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1392_);
v___x_1394_ = l_Lean_Syntax_isNone(v___x_1393_);
if (v___x_1394_ == 0)
{
uint8_t v___x_1395_; 
lean_inc(v___x_1393_);
v___x_1395_ = l_Lean_Syntax_matchesNull(v___x_1393_, v___y_1288_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec(v___x_1393_);
lean_dec(v___x_1391_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1396_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = l_Lean_Syntax_getArg(v___x_1393_, v___x_425_);
lean_dec(v___x_1393_);
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1397_);
v___x_1399_ = l_Lean_Syntax_isOfKind(v___x_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec(v___x_1397_);
lean_dec(v___x_1391_);
lean_dec_ref(v___y_1290_);
lean_dec(v_attrs_x3f_1289_);
lean_dec(v___y_1287_);
lean_dec(v_stx_147_);
v___x_1400_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1291_);
return v___x_1400_;
}
else
{
lean_object* v_name_1401_; lean_object* v___x_1402_; 
v_name_1401_ = l_Lean_Syntax_getArg(v___x_1397_, v___x_1301_);
lean_dec(v___x_1397_);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_name_1401_);
v___y_1263_ = v___x_1391_;
v___y_1264_ = v___x_1295_;
v___y_1265_ = v___x_1388_;
v___y_1266_ = v___y_1288_;
v___y_1267_ = v___x_1294_;
v___y_1268_ = v___y_1287_;
v___y_1269_ = v_attrs_x3f_1289_;
v___y_1270_ = v___x_1301_;
v_name_1271_ = v___x_1402_;
v___y_1272_ = v___y_1290_;
v___y_1273_ = v___y_1291_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v___x_1403_; 
lean_dec(v___x_1393_);
v___x_1403_ = lean_box(0);
v___y_1263_ = v___x_1391_;
v___y_1264_ = v___x_1295_;
v___y_1265_ = v___x_1388_;
v___y_1266_ = v___y_1288_;
v___y_1267_ = v___x_1294_;
v___y_1268_ = v___y_1287_;
v___y_1269_ = v_attrs_x3f_1289_;
v___y_1270_ = v___x_1301_;
v_name_1271_ = v___x_1403_;
v___y_1272_ = v___y_1290_;
v___y_1273_ = v___y_1291_;
goto v___jp_1262_;
}
}
}
}
}
}
v___jp_1404_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = l_Lean_Syntax_getArg(v_stx_147_, v___x_1408_);
v___x_1410_ = l_Lean_Syntax_isNone(v___x_1409_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
lean_inc(v___x_1409_);
v___x_1411_ = l_Lean_Syntax_matchesNull(v___x_1409_, v___x_1408_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_dec(v___x_1409_);
lean_dec_ref(v___y_1406_);
lean_dec(v_doc_x3f_1405_);
lean_dec(v_stx_147_);
v___x_1412_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1407_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = l_Lean_Syntax_getArg(v___x_1409_, v___x_425_);
lean_dec(v___x_1409_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(v___x_1413_);
v___x_1415_ = l_Lean_Syntax_isOfKind(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_dec(v___x_1413_);
lean_dec_ref(v___y_1406_);
lean_dec(v_doc_x3f_1405_);
lean_dec(v_stx_147_);
v___x_1416_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1407_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; lean_object* v_attrs_x3f_1418_; lean_object* v___x_1419_; 
v___x_1417_ = l_Lean_Syntax_getArg(v___x_1413_, v___x_1408_);
lean_dec(v___x_1413_);
v_attrs_x3f_1418_ = l_Lean_Syntax_getArgs(v___x_1417_);
lean_dec(v___x_1417_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_attrs_x3f_1418_);
v___y_1287_ = v_doc_x3f_1405_;
v___y_1288_ = v___x_1408_;
v_attrs_x3f_1289_ = v___x_1419_;
v___y_1290_ = v___y_1406_;
v___y_1291_ = v___y_1407_;
goto v___jp_1286_;
}
}
}
else
{
lean_object* v___x_1420_; 
lean_dec(v___x_1409_);
v___x_1420_ = lean_box(0);
v___y_1287_ = v_doc_x3f_1405_;
v___y_1288_ = v___x_1408_;
v_attrs_x3f_1289_ = v___x_1420_;
v___y_1290_ = v___y_1406_;
v___y_1291_ = v___y_1407_;
goto v___jp_1286_;
}
}
}
v___jp_152_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_170_ = l_Array_append___redArg(v___y_167_, v___y_169_);
lean_dec_ref(v___y_169_);
lean_inc(v___y_163_);
lean_inc(v___y_155_);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___y_155_);
lean_ctor_set(v___x_171_, 1, v___y_163_);
lean_ctor_set(v___x_171_, 2, v___x_170_);
v___x_172_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_173_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__6, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6);
v___x_174_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
v___x_175_ = l_Lean_addMacroScope(v___y_158_, v___x_174_, v___y_159_);
v___x_176_ = lean_box(0);
lean_inc(v___y_155_);
v___x_177_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_177_, 0, v___y_155_);
lean_ctor_set(v___x_177_, 1, v___x_173_);
lean_ctor_set(v___x_177_, 2, v___x_175_);
lean_ctor_set(v___x_177_, 3, v___x_176_);
lean_inc(v___y_153_);
lean_inc_ref(v___x_177_);
lean_inc(v___y_155_);
v___x_178_ = l_Lean_Syntax_node2(v___y_155_, v___x_172_, v___x_177_, v___y_153_);
lean_inc(v___y_163_);
lean_inc(v___y_155_);
v___x_179_ = l_Lean_Syntax_node2(v___y_155_, v___y_163_, v___x_178_, v___y_165_);
v___x_180_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(v___y_155_);
v___x_181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_181_, 0, v___y_155_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
v___x_183_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_156_, v___x_182_);
lean_inc(v___y_155_);
v___x_184_ = l_Lean_Syntax_node1(v___y_155_, v___y_163_, v___x_177_);
lean_inc(v___y_155_);
v___x_185_ = l_Lean_Syntax_node2(v___y_155_, v___x_183_, v___y_160_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(10u);
v___x_187_ = lean_mk_empty_array_with_capacity(v___x_186_);
v___x_188_ = lean_array_push(v___x_187_, v___y_168_);
v___x_189_ = lean_array_push(v___x_188_, v___y_161_);
v___x_190_ = lean_array_push(v___x_189_, v___y_164_);
v___x_191_ = lean_array_push(v___x_190_, v___y_162_);
v___x_192_ = lean_array_push(v___x_191_, v___y_153_);
v___x_193_ = lean_array_push(v___x_192_, v___y_166_);
v___x_194_ = lean_array_push(v___x_193_, v___x_171_);
v___x_195_ = lean_array_push(v___x_194_, v___x_179_);
v___x_196_ = lean_array_push(v___x_195_, v___x_181_);
v___x_197_ = lean_array_push(v___x_196_, v___x_185_);
v___x_198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_198_, 0, v___y_155_);
lean_ctor_set(v___x_198_, 1, v___y_157_);
lean_ctor_set(v___x_198_, 2, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___y_154_);
return v___x_199_;
}
v___jp_200_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_218_ = l_Array_append___redArg(v___y_215_, v___y_217_);
lean_dec_ref(v___y_217_);
lean_inc(v___y_201_);
lean_inc(v___y_210_);
v___x_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_219_, 0, v___y_210_);
lean_ctor_set(v___x_219_, 1, v___y_201_);
lean_ctor_set(v___x_219_, 2, v___x_218_);
v___x_220_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_221_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__6, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6);
v___x_222_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
v___x_223_ = l_Lean_addMacroScope(v___y_212_, v___x_222_, v___y_207_);
v___x_224_ = lean_box(0);
lean_inc(v___y_210_);
v___x_225_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_225_, 0, v___y_210_);
lean_ctor_set(v___x_225_, 1, v___x_221_);
lean_ctor_set(v___x_225_, 2, v___x_223_);
lean_ctor_set(v___x_225_, 3, v___x_224_);
lean_inc(v___y_203_);
lean_inc_ref(v___x_225_);
lean_inc(v___y_210_);
v___x_226_ = l_Lean_Syntax_node2(v___y_210_, v___x_220_, v___x_225_, v___y_203_);
lean_inc(v___y_201_);
lean_inc(v___y_210_);
v___x_227_ = l_Lean_Syntax_node2(v___y_210_, v___y_201_, v___y_209_, v___x_226_);
v___x_228_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(v___y_210_);
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_210_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
v___x_231_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_202_, v___x_230_);
lean_inc(v___y_210_);
v___x_232_ = l_Lean_Syntax_node1(v___y_210_, v___y_201_, v___x_225_);
lean_inc(v___y_210_);
v___x_233_ = l_Lean_Syntax_node2(v___y_210_, v___x_231_, v___y_216_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(10u);
v___x_235_ = lean_mk_empty_array_with_capacity(v___x_234_);
v___x_236_ = lean_array_push(v___x_235_, v___y_206_);
v___x_237_ = lean_array_push(v___x_236_, v___y_205_);
v___x_238_ = lean_array_push(v___x_237_, v___y_208_);
v___x_239_ = lean_array_push(v___x_238_, v___y_211_);
v___x_240_ = lean_array_push(v___x_239_, v___y_203_);
v___x_241_ = lean_array_push(v___x_240_, v___y_204_);
v___x_242_ = lean_array_push(v___x_241_, v___x_219_);
v___x_243_ = lean_array_push(v___x_242_, v___x_227_);
v___x_244_ = lean_array_push(v___x_243_, v___x_229_);
v___x_245_ = lean_array_push(v___x_244_, v___x_233_);
v___x_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_246_, 0, v___y_210_);
lean_ctor_set(v___x_246_, 1, v___y_213_);
lean_ctor_set(v___x_246_, 2, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___y_214_);
return v___x_247_;
}
v___jp_248_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_269_ = l_Array_append___redArg(v___y_265_, v___y_268_);
lean_dec_ref(v___y_268_);
lean_inc(v___y_262_);
lean_inc(v___y_261_);
v___x_270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_270_, 0, v___y_261_);
lean_ctor_set(v___x_270_, 1, v___y_262_);
lean_ctor_set(v___x_270_, 2, v___x_269_);
v___x_271_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_272_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
v___x_273_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc(v___y_251_);
lean_inc(v___y_259_);
v___x_274_ = l_Lean_addMacroScope(v___y_259_, v___x_273_, v___y_251_);
v___x_275_ = lean_box(0);
lean_inc(v___y_261_);
v___x_276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_276_, 0, v___y_261_);
lean_ctor_set(v___x_276_, 1, v___x_272_);
lean_ctor_set(v___x_276_, 2, v___x_274_);
lean_ctor_set(v___x_276_, 3, v___x_275_);
lean_inc(v___y_261_);
v___x_277_ = l_Lean_Syntax_node2(v___y_261_, v___y_252_, v___y_257_, v___y_258_);
lean_inc(v___y_262_);
lean_inc(v___y_261_);
v___x_278_ = l_Lean_Syntax_node1(v___y_261_, v___y_262_, v___x_277_);
lean_inc_ref(v___x_276_);
lean_inc(v___y_261_);
v___x_279_ = l_Lean_Syntax_node2(v___y_261_, v___x_271_, v___x_276_, v___x_278_);
v___x_280_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
v___x_281_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
v___x_282_ = l_Lean_addMacroScope(v___y_259_, v___x_281_, v___y_251_);
lean_inc(v___y_261_);
v___x_283_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_283_, 0, v___y_261_);
lean_ctor_set(v___x_283_, 1, v___x_280_);
lean_ctor_set(v___x_283_, 2, v___x_282_);
lean_ctor_set(v___x_283_, 3, v___x_275_);
lean_inc(v___y_266_);
lean_inc_ref(v___x_283_);
lean_inc(v___y_261_);
v___x_284_ = l_Lean_Syntax_node2(v___y_261_, v___x_271_, v___x_283_, v___y_266_);
lean_inc(v___y_262_);
lean_inc(v___y_261_);
v___x_285_ = l_Lean_Syntax_node3(v___y_261_, v___y_262_, v___x_279_, v___y_254_, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(v___y_261_);
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v___y_261_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
v___x_289_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_253_, v___x_288_);
lean_inc(v___y_261_);
v___x_290_ = l_Lean_Syntax_node2(v___y_261_, v___y_262_, v___x_276_, v___x_283_);
lean_inc(v___y_261_);
v___x_291_ = l_Lean_Syntax_node2(v___y_261_, v___x_289_, v___y_256_, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(10u);
v___x_293_ = lean_mk_empty_array_with_capacity(v___x_292_);
v___x_294_ = lean_array_push(v___x_293_, v___y_263_);
v___x_295_ = lean_array_push(v___x_294_, v___y_260_);
v___x_296_ = lean_array_push(v___x_295_, v___y_249_);
v___x_297_ = lean_array_push(v___x_296_, v___y_267_);
v___x_298_ = lean_array_push(v___x_297_, v___y_266_);
v___x_299_ = lean_array_push(v___x_298_, v___y_250_);
v___x_300_ = lean_array_push(v___x_299_, v___x_270_);
v___x_301_ = lean_array_push(v___x_300_, v___x_285_);
v___x_302_ = lean_array_push(v___x_301_, v___x_287_);
v___x_303_ = lean_array_push(v___x_302_, v___x_291_);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___y_261_);
lean_ctor_set(v___x_304_, 1, v___y_255_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___y_264_);
return v___x_305_;
}
v___jp_306_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_327_ = l_Array_append___redArg(v___y_320_, v___y_326_);
lean_dec_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc(v___y_317_);
v___x_328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_328_, 0, v___y_317_);
lean_ctor_set(v___x_328_, 1, v___y_325_);
lean_ctor_set(v___x_328_, 2, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_330_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
v___x_331_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc(v___y_316_);
lean_inc(v___y_321_);
v___x_332_ = l_Lean_addMacroScope(v___y_321_, v___x_331_, v___y_316_);
v___x_333_ = lean_box(0);
lean_inc(v___y_317_);
v___x_334_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_334_, 0, v___y_317_);
lean_ctor_set(v___x_334_, 1, v___x_330_);
lean_ctor_set(v___x_334_, 2, v___x_332_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
lean_inc(v___y_317_);
v___x_335_ = l_Lean_Syntax_node2(v___y_317_, v___y_311_, v___y_323_, v___y_313_);
lean_inc(v___y_325_);
lean_inc(v___y_317_);
v___x_336_ = l_Lean_Syntax_node1(v___y_317_, v___y_325_, v___x_335_);
lean_inc(v___x_336_);
lean_inc_ref(v___x_334_);
lean_inc(v___y_317_);
v___x_337_ = l_Lean_Syntax_node2(v___y_317_, v___x_329_, v___x_334_, v___x_336_);
v___x_338_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
v___x_339_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
v___x_340_ = l_Lean_addMacroScope(v___y_321_, v___x_339_, v___y_316_);
lean_inc(v___y_317_);
v___x_341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_341_, 0, v___y_317_);
lean_ctor_set(v___x_341_, 1, v___x_338_);
lean_ctor_set(v___x_341_, 2, v___x_340_);
lean_ctor_set(v___x_341_, 3, v___x_333_);
lean_inc_ref(v___x_341_);
lean_inc(v___y_317_);
v___x_342_ = l_Lean_Syntax_node2(v___y_317_, v___x_329_, v___x_341_, v___x_336_);
lean_inc(v___y_325_);
lean_inc(v___y_317_);
v___x_343_ = l_Lean_Syntax_node3(v___y_317_, v___y_325_, v___x_337_, v___y_312_, v___x_342_);
v___x_344_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(v___y_317_);
v___x_345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_345_, 0, v___y_317_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
v___x_347_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_310_, v___x_346_);
lean_inc(v___y_317_);
v___x_348_ = l_Lean_Syntax_node2(v___y_317_, v___y_325_, v___x_334_, v___x_341_);
lean_inc(v___y_317_);
v___x_349_ = l_Lean_Syntax_node2(v___y_317_, v___x_347_, v___y_308_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(10u);
v___x_351_ = lean_mk_empty_array_with_capacity(v___x_350_);
v___x_352_ = lean_array_push(v___x_351_, v___y_315_);
v___x_353_ = lean_array_push(v___x_352_, v___y_322_);
v___x_354_ = lean_array_push(v___x_353_, v___y_314_);
v___x_355_ = lean_array_push(v___x_354_, v___y_309_);
v___x_356_ = lean_array_push(v___x_355_, v___y_319_);
v___x_357_ = lean_array_push(v___x_356_, v___y_318_);
v___x_358_ = lean_array_push(v___x_357_, v___x_328_);
v___x_359_ = lean_array_push(v___x_358_, v___x_343_);
v___x_360_ = lean_array_push(v___x_359_, v___x_345_);
v___x_361_ = lean_array_push(v___x_360_, v___x_349_);
v___x_362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_362_, 0, v___y_317_);
lean_ctor_set(v___x_362_, 1, v___y_307_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___y_324_);
return v___x_363_;
}
v___jp_364_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_385_ = l_Array_append___redArg(v___y_377_, v___y_384_);
lean_dec_ref(v___y_384_);
lean_inc(v___y_380_);
lean_inc(v___y_369_);
v___x_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_386_, 0, v___y_369_);
lean_ctor_set(v___x_386_, 1, v___y_380_);
lean_ctor_set(v___x_386_, 2, v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_388_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
v___x_389_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc(v___y_370_);
lean_inc(v___y_379_);
v___x_390_ = l_Lean_addMacroScope(v___y_379_, v___x_389_, v___y_370_);
v___x_391_ = lean_box(0);
lean_inc(v___y_369_);
v___x_392_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_392_, 0, v___y_369_);
lean_ctor_set(v___x_392_, 1, v___x_388_);
lean_ctor_set(v___x_392_, 2, v___x_390_);
lean_ctor_set(v___x_392_, 3, v___x_391_);
lean_inc(v___y_365_);
lean_inc_ref(v___x_392_);
lean_inc(v___y_369_);
v___x_393_ = l_Lean_Syntax_node2(v___y_369_, v___x_387_, v___x_392_, v___y_365_);
v___x_394_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
v___x_395_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
v___x_396_ = l_Lean_addMacroScope(v___y_379_, v___x_395_, v___y_370_);
lean_inc(v___y_369_);
v___x_397_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_397_, 0, v___y_369_);
lean_ctor_set(v___x_397_, 1, v___x_394_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
lean_ctor_set(v___x_397_, 3, v___x_391_);
lean_inc(v___y_369_);
v___x_398_ = l_Lean_Syntax_node2(v___y_369_, v___y_376_, v___y_378_, v___y_372_);
lean_inc(v___y_380_);
lean_inc(v___y_369_);
v___x_399_ = l_Lean_Syntax_node1(v___y_369_, v___y_380_, v___x_398_);
lean_inc_ref(v___x_397_);
lean_inc(v___y_369_);
v___x_400_ = l_Lean_Syntax_node2(v___y_369_, v___x_387_, v___x_397_, v___x_399_);
lean_inc(v___y_380_);
lean_inc(v___y_369_);
v___x_401_ = l_Lean_Syntax_node3(v___y_369_, v___y_380_, v___x_393_, v___y_375_, v___x_400_);
v___x_402_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(v___y_369_);
v___x_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_403_, 0, v___y_369_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
v___x_405_ = l_Lean_Name_mkStr4(v___x_150_, v___x_151_, v___y_371_, v___x_404_);
lean_inc(v___y_369_);
v___x_406_ = l_Lean_Syntax_node2(v___y_369_, v___y_380_, v___x_392_, v___x_397_);
lean_inc(v___y_369_);
v___x_407_ = l_Lean_Syntax_node2(v___y_369_, v___x_405_, v___y_374_, v___x_406_);
v___x_408_ = lean_unsigned_to_nat(10u);
v___x_409_ = lean_mk_empty_array_with_capacity(v___x_408_);
v___x_410_ = lean_array_push(v___x_409_, v___y_381_);
v___x_411_ = lean_array_push(v___x_410_, v___y_383_);
v___x_412_ = lean_array_push(v___x_411_, v___y_368_);
v___x_413_ = lean_array_push(v___x_412_, v___y_367_);
v___x_414_ = lean_array_push(v___x_413_, v___y_365_);
v___x_415_ = lean_array_push(v___x_414_, v___y_382_);
v___x_416_ = lean_array_push(v___x_415_, v___x_386_);
v___x_417_ = lean_array_push(v___x_416_, v___x_401_);
v___x_418_ = lean_array_push(v___x_417_, v___x_403_);
v___x_419_ = lean_array_push(v___x_418_, v___x_407_);
v___x_420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_420_, 0, v___y_369_);
lean_ctor_set(v___x_420_, 1, v___y_366_);
lean_ctor_set(v___x_420_, 2, v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___y_373_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix(lean_object* v_stx_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___f_1436_; lean_object* v___x_1437_; 
v___f_1436_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___closed__0));
v___x_1437_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(v_stx_1433_, v___f_1436_, v_a_1434_, v_a_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1(){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1446_ = l_Lean_Elab_macroAttribute;
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17));
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2));
v___x_1449_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMixfix), 3, 0);
v___x_1450_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1446_, v___x_1447_, v___x_1448_, v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___boxed(lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3(){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2));
v___x_1480_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6));
v___x_1481_ = l_Lean_addBuiltinDeclarationRanges(v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
return v_res_1483_;
}
}
lean_object* runtime_initialize_Lean_Elab_Attributes(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Mixfix(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Mixfix(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Attributes(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Mixfix(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Mixfix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Mixfix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Mixfix(builtin);
}
#ifdef __cplusplus
}
#endif
