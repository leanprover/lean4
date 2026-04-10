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
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_mkAttrKindGlobal;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_expandMixfix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_expandMixfix___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_expandMixfix___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "expandMixfix"};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 127, 199, 109, 87, 154, 161, 211)}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object* v_stx_1_, lean_object* v_f_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_attrKind_6_; lean_object* v___x_7_; lean_object* v_stx_8_; lean_object* v___x_9_; 
v___x_5_ = lean_unsigned_to_nat(2u);
v_attrKind_6_ = l_Lean_Syntax_getArg(v_stx_1_, v___x_5_);
v___x_7_ = l_Lean_Elab_mkAttrKindGlobal;
v_stx_8_ = l_Lean_Syntax_setArg(v_stx_1_, v___x_5_, v___x_7_);
lean_inc_ref(v_a_3_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal___boxed(lean_object* v_stx_29_, lean_object* v_f_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(v_stx_29_, v_f_30_, v_a_31_, v_a_32_);
lean_dec_ref(v_a_31_);
return v_res_33_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5));
v___x_45_ = l_String_toRawSubstring_x27(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10));
v___x_52_ = l_String_toRawSubstring_x27(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13));
v___x_57_ = l_String_toRawSubstring_x27(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Array_mkArray0(lean_box(0));
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0(lean_object* v_stx_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_155_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0));
v___x_156_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1));
v___x_427_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17));
lean_inc(v_stx_152_);
v___x_428_ = l_Lean_Syntax_isOfKind(v_stx_152_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec(v_stx_152_);
v___x_429_ = l_Lean_Macro_throwUnsupported___redArg(v___y_154_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v_prio_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; uint8_t v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v_name_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v_prio_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_725_; uint8_t v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v_name_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; uint8_t v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v_prio_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; uint8_t v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v_name_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v_prio_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v_name_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v_prio_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v_name_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v_attrs_x3f_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v_doc_x3f_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_1426_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_430_);
v___x_1427_ = l_Lean_Syntax_isNone(v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1426_);
v___x_1429_ = l_Lean_Syntax_matchesNull(v___x_1426_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec(v___x_1426_);
lean_dec(v_stx_152_);
v___x_1430_ = l_Lean_Macro_throwUnsupported___redArg(v___y_154_);
return v___x_1430_;
}
else
{
lean_object* v_doc_x3f_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_doc_x3f_1431_ = l_Lean_Syntax_getArg(v___x_1426_, v___x_430_);
lean_dec(v___x_1426_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54));
lean_inc(v_doc_x3f_1431_);
v___x_1433_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
lean_dec(v_doc_x3f_1431_);
lean_dec(v_stx_152_);
v___x_1434_ = l_Lean_Macro_throwUnsupported___redArg(v___y_154_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_doc_x3f_1431_);
v_doc_x3f_1410_ = v___x_1435_;
v___y_1411_ = v___y_153_;
v___y_1412_ = v___y_154_;
goto v___jp_1409_;
}
}
}
else
{
lean_object* v___x_1436_; 
lean_dec(v___x_1426_);
v___x_1436_ = lean_box(0);
v_doc_x3f_1410_ = v___x_1436_;
v___y_1411_ = v___y_153_;
v___y_1412_ = v___y_154_;
goto v___jp_1409_;
}
v___jp_431_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_ref(v___y_432_);
v___x_449_ = l_Array_append___redArg(v___y_432_, v___y_448_);
lean_dec_ref(v___y_448_);
lean_inc(v___y_446_);
lean_inc(v___y_439_);
v___x_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_450_, 0, v___y_439_);
lean_ctor_set(v___x_450_, 1, v___y_446_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
if (lean_obj_tag(v___y_441_) == 1)
{
lean_object* v_val_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_val_451_ = lean_ctor_get(v___y_441_, 0);
lean_inc(v_val_451_);
lean_dec_ref(v___y_441_);
v___x_452_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_453_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_439_, 5);
v___x_454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_454_, 0, v___y_439_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
v___x_456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_439_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_458_, 0, v___y_439_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_460_, 0, v___y_439_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_Syntax_node5(v___y_439_, v___x_452_, v___x_454_, v___x_456_, v___x_458_, v_val_451_, v___x_460_);
v___x_462_ = l_Array_mkArray1___redArg(v___x_461_);
v___y_158_ = v___y_432_;
v___y_159_ = v___y_433_;
v___y_160_ = v___y_434_;
v___y_161_ = v___y_435_;
v___y_162_ = v___y_436_;
v___y_163_ = v___y_437_;
v___y_164_ = v___y_438_;
v___y_165_ = v___y_439_;
v___y_166_ = v___y_440_;
v___y_167_ = v___y_442_;
v___y_168_ = v___y_443_;
v___y_169_ = v___y_444_;
v___y_170_ = v___y_445_;
v___y_171_ = v___y_446_;
v___y_172_ = v___x_450_;
v___y_173_ = v___y_447_;
v___y_174_ = v___x_462_;
goto v___jp_157_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v___y_441_);
v___x_463_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_158_ = v___y_432_;
v___y_159_ = v___y_433_;
v___y_160_ = v___y_434_;
v___y_161_ = v___y_435_;
v___y_162_ = v___y_436_;
v___y_163_ = v___y_437_;
v___y_164_ = v___y_438_;
v___y_165_ = v___y_439_;
v___y_166_ = v___y_440_;
v___y_167_ = v___y_442_;
v___y_168_ = v___y_443_;
v___y_169_ = v___y_444_;
v___y_170_ = v___y_445_;
v___y_171_ = v___y_446_;
v___y_172_ = v___x_450_;
v___y_173_ = v___y_447_;
v___y_174_ = v___x_463_;
goto v___jp_157_;
}
}
v___jp_464_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc_ref_n(v___y_465_, 2);
v___x_483_ = l_Array_append___redArg(v___y_465_, v___y_482_);
lean_dec_ref(v___y_482_);
lean_inc_n(v___y_480_, 3);
lean_inc_n(v___y_475_, 7);
v___x_484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_484_, 0, v___y_475_);
lean_ctor_set(v___x_484_, 1, v___y_480_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
v___x_485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_485_, 0, v___y_475_);
lean_ctor_set(v___x_485_, 1, v___y_480_);
lean_ctor_set(v___x_485_, 2, v___y_465_);
lean_inc(v___y_473_);
v___x_486_ = l_Lean_Syntax_node1(v___y_475_, v___y_473_, v___x_485_);
lean_inc_ref(v___y_469_);
v___x_487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_487_, 0, v___y_475_);
lean_ctor_set(v___x_487_, 1, v___y_469_);
v___x_488_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
v___x_489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_489_, 0, v___y_475_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
lean_inc(v___y_470_);
v___x_490_ = l_Lean_Syntax_node2(v___y_475_, v___y_470_, v___x_489_, v___y_466_);
v___x_491_ = l_Lean_Syntax_node1(v___y_475_, v___y_480_, v___x_490_);
if (lean_obj_tag(v___y_468_) == 1)
{
lean_object* v_val_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_val_492_ = lean_ctor_get(v___y_468_, 0);
lean_inc(v_val_492_);
lean_dec_ref(v___y_468_);
v___x_493_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_494_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_475_, 5);
v___x_495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_495_, 0, v___y_475_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
v___x_497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_497_, 0, v___y_475_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_499_, 0, v___y_475_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___y_475_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_Syntax_node5(v___y_475_, v___x_493_, v___x_495_, v___x_497_, v___x_499_, v_val_492_, v___x_501_);
v___x_503_ = l_Array_mkArray1___redArg(v___x_502_);
v___y_432_ = v___y_465_;
v___y_433_ = v___x_491_;
v___y_434_ = v___y_467_;
v___y_435_ = v___y_471_;
v___y_436_ = v___y_472_;
v___y_437_ = v___x_486_;
v___y_438_ = v___y_474_;
v___y_439_ = v___y_475_;
v___y_440_ = v___y_476_;
v___y_441_ = v___y_478_;
v___y_442_ = v___y_477_;
v___y_443_ = v___x_484_;
v___y_444_ = v___x_487_;
v___y_445_ = v___y_479_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_481_;
v___y_448_ = v___x_503_;
goto v___jp_431_;
}
else
{
lean_object* v___x_504_; 
lean_dec(v___y_468_);
v___x_504_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_432_ = v___y_465_;
v___y_433_ = v___x_491_;
v___y_434_ = v___y_467_;
v___y_435_ = v___y_471_;
v___y_436_ = v___y_472_;
v___y_437_ = v___x_486_;
v___y_438_ = v___y_474_;
v___y_439_ = v___y_475_;
v___y_440_ = v___y_476_;
v___y_441_ = v___y_478_;
v___y_442_ = v___y_477_;
v___y_443_ = v___x_484_;
v___y_444_ = v___x_487_;
v___y_445_ = v___y_479_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_481_;
v___y_448_ = v___x_504_;
goto v___jp_431_;
}
}
v___jp_505_:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc_ref(v___y_506_);
v___x_524_ = l_Array_append___redArg(v___y_506_, v___y_523_);
lean_dec_ref(v___y_523_);
lean_inc(v___y_521_);
lean_inc(v___y_516_);
v___x_525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_525_, 0, v___y_516_);
lean_ctor_set(v___x_525_, 1, v___y_521_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
if (lean_obj_tag(v___y_512_) == 1)
{
lean_object* v_val_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_val_526_ = lean_ctor_get(v___y_512_, 0);
lean_inc(v_val_526_);
lean_dec_ref(v___y_512_);
v___x_527_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_517_);
v___x_528_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_517_, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_n(v___y_516_, 4);
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_516_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_inc_ref(v___y_506_);
v___x_531_ = l_Array_append___redArg(v___y_506_, v_val_526_);
lean_dec(v_val_526_);
lean_inc(v___y_521_);
v___x_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_532_, 0, v___y_516_);
lean_ctor_set(v___x_532_, 1, v___y_521_);
lean_ctor_set(v___x_532_, 2, v___x_531_);
v___x_533_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_516_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_Syntax_node3(v___y_516_, v___x_528_, v___x_530_, v___x_532_, v___x_534_);
v___x_536_ = l_Array_mkArray1___redArg(v___x_535_);
v___y_465_ = v___y_506_;
v___y_466_ = v___y_507_;
v___y_467_ = v___y_508_;
v___y_468_ = v___y_509_;
v___y_469_ = v___y_510_;
v___y_470_ = v___y_511_;
v___y_471_ = v___y_513_;
v___y_472_ = v___y_514_;
v___y_473_ = v___y_515_;
v___y_474_ = v___x_525_;
v___y_475_ = v___y_516_;
v___y_476_ = v___y_517_;
v___y_477_ = v___y_519_;
v___y_478_ = v___y_518_;
v___y_479_ = v___y_520_;
v___y_480_ = v___y_521_;
v___y_481_ = v___y_522_;
v___y_482_ = v___x_536_;
goto v___jp_464_;
}
else
{
lean_object* v___x_537_; 
lean_dec(v___y_512_);
v___x_537_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_465_ = v___y_506_;
v___y_466_ = v___y_507_;
v___y_467_ = v___y_508_;
v___y_468_ = v___y_509_;
v___y_469_ = v___y_510_;
v___y_470_ = v___y_511_;
v___y_471_ = v___y_513_;
v___y_472_ = v___y_514_;
v___y_473_ = v___y_515_;
v___y_474_ = v___x_525_;
v___y_475_ = v___y_516_;
v___y_476_ = v___y_517_;
v___y_477_ = v___y_519_;
v___y_478_ = v___y_518_;
v___y_479_ = v___y_520_;
v___y_480_ = v___y_521_;
v___y_481_ = v___y_522_;
v___y_482_ = v___x_537_;
goto v___jp_464_;
}
}
v___jp_538_:
{
lean_object* v_quotContext_550_; lean_object* v_currMacroScope_551_; lean_object* v_ref_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_quotContext_550_ = lean_ctor_get(v___y_548_, 1);
v_currMacroScope_551_ = lean_ctor_get(v___y_548_, 2);
v_ref_552_ = lean_ctor_get(v___y_548_, 5);
v___x_553_ = lean_unsigned_to_nat(7u);
v___x_554_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_553_);
v___x_555_ = lean_unsigned_to_nat(9u);
v___x_556_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_555_);
lean_dec(v_stx_152_);
v___x_557_ = l_Lean_SourceInfo_fromRef(v_ref_552_, v___y_542_);
v___x_558_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_559_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_560_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_561_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_546_) == 1)
{
lean_object* v_val_562_; lean_object* v___x_563_; 
v_val_562_ = lean_ctor_get(v___y_546_, 0);
lean_inc(v_val_562_);
lean_dec_ref(v___y_546_);
v___x_563_ = l_Array_mkArray1___redArg(v_val_562_);
v___y_506_ = v___x_561_;
v___y_507_ = v___y_541_;
v___y_508_ = v___x_556_;
v___y_509_ = v___y_543_;
v___y_510_ = v___x_558_;
v___y_511_ = v___y_544_;
v___y_512_ = v___y_545_;
v___y_513_ = v_quotContext_550_;
v___y_514_ = v_currMacroScope_551_;
v___y_515_ = v___y_539_;
v___y_516_ = v___x_557_;
v___y_517_ = v___y_540_;
v___y_518_ = v_prio_547_;
v___y_519_ = v___x_559_;
v___y_520_ = v___y_549_;
v___y_521_ = v___x_560_;
v___y_522_ = v___x_554_;
v___y_523_ = v___x_563_;
goto v___jp_505_;
}
else
{
lean_object* v___x_564_; 
lean_dec(v___y_546_);
v___x_564_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_506_ = v___x_561_;
v___y_507_ = v___y_541_;
v___y_508_ = v___x_556_;
v___y_509_ = v___y_543_;
v___y_510_ = v___x_558_;
v___y_511_ = v___y_544_;
v___y_512_ = v___y_545_;
v___y_513_ = v_quotContext_550_;
v___y_514_ = v_currMacroScope_551_;
v___y_515_ = v___y_539_;
v___y_516_ = v___x_557_;
v___y_517_ = v___y_540_;
v___y_518_ = v_prio_547_;
v___y_519_ = v___x_559_;
v___y_520_ = v___y_549_;
v___y_521_ = v___x_560_;
v___y_522_ = v___x_554_;
v___y_523_ = v___x_564_;
goto v___jp_505_;
}
}
v___jp_565_:
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(6u);
v___x_579_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_578_);
v___x_580_ = l_Lean_Syntax_isNone(v___x_579_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; 
lean_inc(v___x_579_);
v___x_581_ = l_Lean_Syntax_matchesNull(v___x_579_, v___y_571_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v___x_579_);
lean_dec(v_name_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
lean_dec(v___y_569_);
lean_dec(v_stx_152_);
v___x_582_ = l_Lean_Macro_throwUnsupported___redArg(v___y_577_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = l_Lean_Syntax_getArg(v___x_579_, v___x_430_);
lean_dec(v___x_579_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_583_);
v___x_585_ = l_Lean_Syntax_isOfKind(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec(v___x_583_);
lean_dec(v_name_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
lean_dec(v___y_569_);
lean_dec(v_stx_152_);
v___x_586_ = l_Lean_Macro_throwUnsupported___redArg(v___y_577_);
return v___x_586_;
}
else
{
lean_object* v_prio_587_; lean_object* v___x_588_; 
v_prio_587_ = l_Lean_Syntax_getArg(v___x_583_, v___y_566_);
lean_dec(v___x_583_);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v_prio_587_);
v___y_539_ = v___y_567_;
v___y_540_ = v___y_568_;
v___y_541_ = v___y_569_;
v___y_542_ = v___y_570_;
v___y_543_ = v_name_575_;
v___y_544_ = v___y_572_;
v___y_545_ = v___y_573_;
v___y_546_ = v___y_574_;
v_prio_547_ = v___x_588_;
v___y_548_ = v___y_576_;
v___y_549_ = v___y_577_;
goto v___jp_538_;
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec(v___x_579_);
v___x_589_ = lean_box(0);
v___y_539_ = v___y_567_;
v___y_540_ = v___y_568_;
v___y_541_ = v___y_569_;
v___y_542_ = v___y_570_;
v___y_543_ = v_name_575_;
v___y_544_ = v___y_572_;
v___y_545_ = v___y_573_;
v___y_546_ = v___y_574_;
v_prio_547_ = v___x_589_;
v___y_548_ = v___y_576_;
v___y_549_ = v___y_577_;
goto v___jp_538_;
}
}
v___jp_590_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_inc_ref(v___y_598_);
v___x_608_ = l_Array_append___redArg(v___y_598_, v___y_607_);
lean_dec_ref(v___y_607_);
lean_inc(v___y_605_);
lean_inc(v___y_604_);
v___x_609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_609_, 0, v___y_604_);
lean_ctor_set(v___x_609_, 1, v___y_605_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
if (lean_obj_tag(v___y_592_) == 1)
{
lean_object* v_val_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_val_610_ = lean_ctor_get(v___y_592_, 0);
lean_inc(v_val_610_);
lean_dec_ref(v___y_592_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_612_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_604_, 5);
v___x_613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_613_, 0, v___y_604_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
v___x_615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_615_, 0, v___y_604_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___y_604_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_619_, 0, v___y_604_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_Syntax_node5(v___y_604_, v___x_611_, v___x_613_, v___x_615_, v___x_617_, v_val_610_, v___x_619_);
v___x_621_ = l_Array_mkArray1___redArg(v___x_620_);
v___y_206_ = v___y_591_;
v___y_207_ = v___y_593_;
v___y_208_ = v___y_594_;
v___y_209_ = v___y_595_;
v___y_210_ = v___y_596_;
v___y_211_ = v___y_597_;
v___y_212_ = v___y_598_;
v___y_213_ = v___y_599_;
v___y_214_ = v___y_600_;
v___y_215_ = v___y_601_;
v___y_216_ = v___y_602_;
v___y_217_ = v___y_603_;
v___y_218_ = v___y_604_;
v___y_219_ = v___x_609_;
v___y_220_ = v___y_605_;
v___y_221_ = v___y_606_;
v___y_222_ = v___x_621_;
goto v___jp_205_;
}
else
{
lean_object* v___x_622_; 
lean_dec(v___y_592_);
v___x_622_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_206_ = v___y_591_;
v___y_207_ = v___y_593_;
v___y_208_ = v___y_594_;
v___y_209_ = v___y_595_;
v___y_210_ = v___y_596_;
v___y_211_ = v___y_597_;
v___y_212_ = v___y_598_;
v___y_213_ = v___y_599_;
v___y_214_ = v___y_600_;
v___y_215_ = v___y_601_;
v___y_216_ = v___y_602_;
v___y_217_ = v___y_603_;
v___y_218_ = v___y_604_;
v___y_219_ = v___x_609_;
v___y_220_ = v___y_605_;
v___y_221_ = v___y_606_;
v___y_222_ = v___x_622_;
goto v___jp_205_;
}
}
v___jp_623_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_inc_ref_n(v___y_630_, 2);
v___x_642_ = l_Array_append___redArg(v___y_630_, v___y_641_);
lean_dec_ref(v___y_641_);
lean_inc_n(v___y_639_, 3);
lean_inc_n(v___y_635_, 7);
v___x_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_643_, 0, v___y_635_);
lean_ctor_set(v___x_643_, 1, v___y_639_);
lean_ctor_set(v___x_643_, 2, v___x_642_);
v___x_644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_644_, 0, v___y_635_);
lean_ctor_set(v___x_644_, 1, v___y_639_);
lean_ctor_set(v___x_644_, 2, v___y_630_);
lean_inc(v___y_629_);
v___x_645_ = l_Lean_Syntax_node1(v___y_635_, v___y_629_, v___x_644_);
lean_inc_ref(v___y_637_);
v___x_646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_635_);
lean_ctor_set(v___x_646_, 1, v___y_637_);
v___x_647_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_635_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
lean_inc(v___y_625_);
v___x_649_ = l_Lean_Syntax_node2(v___y_635_, v___y_625_, v___x_648_, v___y_638_);
v___x_650_ = l_Lean_Syntax_node1(v___y_635_, v___y_639_, v___x_649_);
if (lean_obj_tag(v___y_636_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_val_651_ = lean_ctor_get(v___y_636_, 0);
lean_inc(v_val_651_);
lean_dec_ref(v___y_636_);
v___x_652_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_653_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_635_, 5);
v___x_654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_654_, 0, v___y_635_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
v___x_656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_656_, 0, v___y_635_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_658_, 0, v___y_635_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_660_, 0, v___y_635_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = l_Lean_Syntax_node5(v___y_635_, v___x_652_, v___x_654_, v___x_656_, v___x_658_, v_val_651_, v___x_660_);
v___x_662_ = l_Array_mkArray1___redArg(v___x_661_);
v___y_591_ = v___y_624_;
v___y_592_ = v___y_626_;
v___y_593_ = v___x_650_;
v___y_594_ = v___x_646_;
v___y_595_ = v___x_643_;
v___y_596_ = v___y_627_;
v___y_597_ = v___y_628_;
v___y_598_ = v___y_630_;
v___y_599_ = v___y_631_;
v___y_600_ = v___y_632_;
v___y_601_ = v___y_633_;
v___y_602_ = v___x_645_;
v___y_603_ = v___y_634_;
v___y_604_ = v___y_635_;
v___y_605_ = v___y_639_;
v___y_606_ = v___y_640_;
v___y_607_ = v___x_662_;
goto v___jp_590_;
}
else
{
lean_object* v___x_663_; 
lean_dec(v___y_636_);
v___x_663_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_591_ = v___y_624_;
v___y_592_ = v___y_626_;
v___y_593_ = v___x_650_;
v___y_594_ = v___x_646_;
v___y_595_ = v___x_643_;
v___y_596_ = v___y_627_;
v___y_597_ = v___y_628_;
v___y_598_ = v___y_630_;
v___y_599_ = v___y_631_;
v___y_600_ = v___y_632_;
v___y_601_ = v___y_633_;
v___y_602_ = v___x_645_;
v___y_603_ = v___y_634_;
v___y_604_ = v___y_635_;
v___y_605_ = v___y_639_;
v___y_606_ = v___y_640_;
v___y_607_ = v___x_663_;
goto v___jp_590_;
}
}
v___jp_664_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc_ref(v___y_672_);
v___x_683_ = l_Array_append___redArg(v___y_672_, v___y_682_);
lean_dec_ref(v___y_682_);
lean_inc(v___y_680_);
lean_inc(v___y_676_);
v___x_684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_684_, 0, v___y_676_);
lean_ctor_set(v___x_684_, 1, v___y_680_);
lean_ctor_set(v___x_684_, 2, v___x_683_);
if (lean_obj_tag(v___y_668_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_val_685_ = lean_ctor_get(v___y_668_, 0);
lean_inc(v_val_685_);
lean_dec_ref(v___y_668_);
v___x_686_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_674_);
v___x_687_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_674_, v___x_686_);
v___x_688_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_n(v___y_676_, 4);
v___x_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_689_, 0, v___y_676_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
lean_inc_ref(v___y_672_);
v___x_690_ = l_Array_append___redArg(v___y_672_, v_val_685_);
lean_dec(v_val_685_);
lean_inc(v___y_680_);
v___x_691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_691_, 0, v___y_676_);
lean_ctor_set(v___x_691_, 1, v___y_680_);
lean_ctor_set(v___x_691_, 2, v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
v___x_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_693_, 0, v___y_676_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_Syntax_node3(v___y_676_, v___x_687_, v___x_689_, v___x_691_, v___x_693_);
v___x_695_ = l_Array_mkArray1___redArg(v___x_694_);
v___y_624_ = v___y_665_;
v___y_625_ = v___y_666_;
v___y_626_ = v___y_667_;
v___y_627_ = v___y_669_;
v___y_628_ = v___y_670_;
v___y_629_ = v___y_671_;
v___y_630_ = v___y_672_;
v___y_631_ = v___y_673_;
v___y_632_ = v___x_684_;
v___y_633_ = v___y_674_;
v___y_634_ = v___y_675_;
v___y_635_ = v___y_676_;
v___y_636_ = v___y_678_;
v___y_637_ = v___y_677_;
v___y_638_ = v___y_679_;
v___y_639_ = v___y_680_;
v___y_640_ = v___y_681_;
v___y_641_ = v___x_695_;
goto v___jp_623_;
}
else
{
lean_object* v___x_696_; 
lean_dec(v___y_668_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_624_ = v___y_665_;
v___y_625_ = v___y_666_;
v___y_626_ = v___y_667_;
v___y_627_ = v___y_669_;
v___y_628_ = v___y_670_;
v___y_629_ = v___y_671_;
v___y_630_ = v___y_672_;
v___y_631_ = v___y_673_;
v___y_632_ = v___x_684_;
v___y_633_ = v___y_674_;
v___y_634_ = v___y_675_;
v___y_635_ = v___y_676_;
v___y_636_ = v___y_678_;
v___y_637_ = v___y_677_;
v___y_638_ = v___y_679_;
v___y_639_ = v___y_680_;
v___y_640_ = v___y_681_;
v___y_641_ = v___x_696_;
goto v___jp_623_;
}
}
v___jp_697_:
{
lean_object* v_quotContext_709_; lean_object* v_currMacroScope_710_; lean_object* v_ref_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_quotContext_709_ = lean_ctor_get(v___y_707_, 1);
v_currMacroScope_710_ = lean_ctor_get(v___y_707_, 2);
v_ref_711_ = lean_ctor_get(v___y_707_, 5);
v___x_712_ = lean_unsigned_to_nat(7u);
v___x_713_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_712_);
v___x_714_ = lean_unsigned_to_nat(9u);
v___x_715_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_714_);
lean_dec(v_stx_152_);
v___x_716_ = l_Lean_SourceInfo_fromRef(v_ref_711_, v___y_699_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_718_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_719_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_720_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_705_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; 
v_val_721_ = lean_ctor_get(v___y_705_, 0);
lean_inc(v_val_721_);
lean_dec_ref(v___y_705_);
v___x_722_ = l_Array_mkArray1___redArg(v_val_721_);
v___y_665_ = v___y_708_;
v___y_666_ = v___y_700_;
v___y_667_ = v_prio_706_;
v___y_668_ = v___y_704_;
v___y_669_ = v___x_715_;
v___y_670_ = v_quotContext_709_;
v___y_671_ = v___y_698_;
v___y_672_ = v___x_720_;
v___y_673_ = v___x_713_;
v___y_674_ = v___y_701_;
v___y_675_ = v_currMacroScope_710_;
v___y_676_ = v___x_716_;
v___y_677_ = v___x_717_;
v___y_678_ = v___y_702_;
v___y_679_ = v___y_703_;
v___y_680_ = v___x_719_;
v___y_681_ = v___x_718_;
v___y_682_ = v___x_722_;
goto v___jp_664_;
}
else
{
lean_object* v___x_723_; 
lean_dec(v___y_705_);
v___x_723_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_665_ = v___y_708_;
v___y_666_ = v___y_700_;
v___y_667_ = v_prio_706_;
v___y_668_ = v___y_704_;
v___y_669_ = v___x_715_;
v___y_670_ = v_quotContext_709_;
v___y_671_ = v___y_698_;
v___y_672_ = v___x_720_;
v___y_673_ = v___x_713_;
v___y_674_ = v___y_701_;
v___y_675_ = v_currMacroScope_710_;
v___y_676_ = v___x_716_;
v___y_677_ = v___x_717_;
v___y_678_ = v___y_702_;
v___y_679_ = v___y_703_;
v___y_680_ = v___x_719_;
v___y_681_ = v___x_718_;
v___y_682_ = v___x_723_;
goto v___jp_664_;
}
}
v___jp_724_:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(6u);
v___x_738_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_737_);
v___x_739_ = l_Lean_Syntax_isNone(v___x_738_);
if (v___x_739_ == 0)
{
uint8_t v___x_740_; 
lean_inc(v___x_738_);
v___x_740_ = l_Lean_Syntax_matchesNull(v___x_738_, v___y_730_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v___x_738_);
lean_dec(v_name_734_);
lean_dec(v___y_733_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec(v_stx_152_);
v___x_741_ = l_Lean_Macro_throwUnsupported___redArg(v___y_736_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = l_Lean_Syntax_getArg(v___x_738_, v___x_430_);
lean_dec(v___x_738_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_742_);
v___x_744_ = l_Lean_Syntax_isOfKind(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec(v___x_742_);
lean_dec(v_name_734_);
lean_dec(v___y_733_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec(v_stx_152_);
v___x_745_ = l_Lean_Macro_throwUnsupported___redArg(v___y_736_);
return v___x_745_;
}
else
{
lean_object* v_prio_746_; lean_object* v___x_747_; 
v_prio_746_ = l_Lean_Syntax_getArg(v___x_742_, v___y_725_);
lean_dec(v___x_742_);
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v_prio_746_);
v___y_698_ = v___y_727_;
v___y_699_ = v___y_726_;
v___y_700_ = v___y_728_;
v___y_701_ = v___y_729_;
v___y_702_ = v_name_734_;
v___y_703_ = v___y_731_;
v___y_704_ = v___y_732_;
v___y_705_ = v___y_733_;
v_prio_706_ = v___x_747_;
v___y_707_ = v___y_735_;
v___y_708_ = v___y_736_;
goto v___jp_697_;
}
}
}
else
{
lean_object* v___x_748_; 
lean_dec(v___x_738_);
v___x_748_ = lean_box(0);
v___y_698_ = v___y_727_;
v___y_699_ = v___y_726_;
v___y_700_ = v___y_728_;
v___y_701_ = v___y_729_;
v___y_702_ = v_name_734_;
v___y_703_ = v___y_731_;
v___y_704_ = v___y_732_;
v___y_705_ = v___y_733_;
v_prio_706_ = v___x_748_;
v___y_707_ = v___y_735_;
v___y_708_ = v___y_736_;
goto v___jp_697_;
}
}
v___jp_749_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc_ref(v___y_758_);
v___x_770_ = l_Array_append___redArg(v___y_758_, v___y_769_);
lean_dec_ref(v___y_769_);
lean_inc(v___y_766_);
lean_inc(v___y_759_);
v___x_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_771_, 0, v___y_759_);
lean_ctor_set(v___x_771_, 1, v___y_766_);
lean_ctor_set(v___x_771_, 2, v___x_770_);
if (lean_obj_tag(v___y_763_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_val_772_ = lean_ctor_get(v___y_763_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v___y_763_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_774_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_759_, 5);
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v___y_759_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_759_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_779_, 0, v___y_759_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___y_759_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_Syntax_node5(v___y_759_, v___x_773_, v___x_775_, v___x_777_, v___x_779_, v_val_772_, v___x_781_);
v___x_783_ = l_Array_mkArray1___redArg(v___x_782_);
v___y_254_ = v___y_750_;
v___y_255_ = v___y_751_;
v___y_256_ = v___y_752_;
v___y_257_ = v___y_753_;
v___y_258_ = v___y_754_;
v___y_259_ = v___y_755_;
v___y_260_ = v___y_756_;
v___y_261_ = v___y_757_;
v___y_262_ = v___y_758_;
v___y_263_ = v___y_759_;
v___y_264_ = v___y_760_;
v___y_265_ = v___y_762_;
v___y_266_ = v___y_761_;
v___y_267_ = v___y_766_;
v___y_268_ = v___y_765_;
v___y_269_ = v___y_764_;
v___y_270_ = v___y_767_;
v___y_271_ = v___x_771_;
v___y_272_ = v___y_768_;
v___y_273_ = v___x_783_;
goto v___jp_253_;
}
else
{
lean_object* v___x_784_; 
lean_dec(v___y_763_);
v___x_784_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_254_ = v___y_750_;
v___y_255_ = v___y_751_;
v___y_256_ = v___y_752_;
v___y_257_ = v___y_753_;
v___y_258_ = v___y_754_;
v___y_259_ = v___y_755_;
v___y_260_ = v___y_756_;
v___y_261_ = v___y_757_;
v___y_262_ = v___y_758_;
v___y_263_ = v___y_759_;
v___y_264_ = v___y_760_;
v___y_265_ = v___y_762_;
v___y_266_ = v___y_761_;
v___y_267_ = v___y_766_;
v___y_268_ = v___y_765_;
v___y_269_ = v___y_764_;
v___y_270_ = v___y_767_;
v___y_271_ = v___x_771_;
v___y_272_ = v___y_768_;
v___y_273_ = v___x_784_;
goto v___jp_253_;
}
}
v___jp_785_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_inc_ref_n(v___y_793_, 2);
v___x_805_ = l_Array_append___redArg(v___y_793_, v___y_804_);
lean_dec_ref(v___y_804_);
lean_inc_n(v___y_800_, 3);
lean_inc_n(v___y_794_, 7);
v___x_806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_806_, 0, v___y_794_);
lean_ctor_set(v___x_806_, 1, v___y_800_);
lean_ctor_set(v___x_806_, 2, v___x_805_);
v___x_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_807_, 0, v___y_794_);
lean_ctor_set(v___x_807_, 1, v___y_800_);
lean_ctor_set(v___x_807_, 2, v___y_793_);
lean_inc(v___y_790_);
v___x_808_ = l_Lean_Syntax_node1(v___y_794_, v___y_790_, v___x_807_);
lean_inc_ref(v___y_788_);
v___x_809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_809_, 0, v___y_794_);
lean_ctor_set(v___x_809_, 1, v___y_788_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
v___x_811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_811_, 0, v___y_794_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
lean_inc_ref(v___x_811_);
lean_inc(v___y_791_);
v___x_812_ = l_Lean_Syntax_node2(v___y_794_, v___y_791_, v___x_811_, v___y_801_);
v___x_813_ = l_Lean_Syntax_node1(v___y_794_, v___y_800_, v___x_812_);
if (lean_obj_tag(v___y_802_) == 1)
{
lean_object* v_val_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_val_814_ = lean_ctor_get(v___y_802_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v___y_802_);
v___x_815_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_816_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_794_, 5);
v___x_817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_817_, 0, v___y_794_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
v___x_819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_819_, 0, v___y_794_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_821_, 0, v___y_794_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_794_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_Syntax_node5(v___y_794_, v___x_815_, v___x_817_, v___x_819_, v___x_821_, v_val_814_, v___x_823_);
v___x_825_ = l_Array_mkArray1___redArg(v___x_824_);
v___y_750_ = v___y_786_;
v___y_751_ = v___y_787_;
v___y_752_ = v___x_811_;
v___y_753_ = v___y_789_;
v___y_754_ = v___x_809_;
v___y_755_ = v___x_806_;
v___y_756_ = v___y_791_;
v___y_757_ = v___y_792_;
v___y_758_ = v___y_793_;
v___y_759_ = v___y_794_;
v___y_760_ = v___y_795_;
v___y_761_ = v___y_797_;
v___y_762_ = v___y_796_;
v___y_763_ = v___y_799_;
v___y_764_ = v___y_798_;
v___y_765_ = v___x_813_;
v___y_766_ = v___y_800_;
v___y_767_ = v___y_803_;
v___y_768_ = v___x_808_;
v___y_769_ = v___x_825_;
goto v___jp_749_;
}
else
{
lean_object* v___x_826_; 
lean_dec(v___y_802_);
v___x_826_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_750_ = v___y_786_;
v___y_751_ = v___y_787_;
v___y_752_ = v___x_811_;
v___y_753_ = v___y_789_;
v___y_754_ = v___x_809_;
v___y_755_ = v___x_806_;
v___y_756_ = v___y_791_;
v___y_757_ = v___y_792_;
v___y_758_ = v___y_793_;
v___y_759_ = v___y_794_;
v___y_760_ = v___y_795_;
v___y_761_ = v___y_797_;
v___y_762_ = v___y_796_;
v___y_763_ = v___y_799_;
v___y_764_ = v___y_798_;
v___y_765_ = v___x_813_;
v___y_766_ = v___y_800_;
v___y_767_ = v___y_803_;
v___y_768_ = v___x_808_;
v___y_769_ = v___x_826_;
goto v___jp_749_;
}
}
v___jp_827_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_inc_ref(v___y_836_);
v___x_847_ = l_Array_append___redArg(v___y_836_, v___y_846_);
lean_dec_ref(v___y_846_);
lean_inc(v___y_842_);
lean_inc(v___y_837_);
v___x_848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_848_, 0, v___y_837_);
lean_ctor_set(v___x_848_, 1, v___y_842_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
if (lean_obj_tag(v___y_831_) == 1)
{
lean_object* v_val_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_val_849_ = lean_ctor_get(v___y_831_, 0);
lean_inc(v_val_849_);
lean_dec_ref(v___y_831_);
v___x_850_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_838_);
v___x_851_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_838_, v___x_850_);
v___x_852_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_n(v___y_837_, 4);
v___x_853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_853_, 0, v___y_837_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
lean_inc_ref(v___y_836_);
v___x_854_ = l_Array_append___redArg(v___y_836_, v_val_849_);
lean_dec(v_val_849_);
lean_inc(v___y_842_);
v___x_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_855_, 0, v___y_837_);
lean_ctor_set(v___x_855_, 1, v___y_842_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
v___x_856_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
v___x_857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_857_, 0, v___y_837_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_Syntax_node3(v___y_837_, v___x_851_, v___x_853_, v___x_855_, v___x_857_);
v___x_859_ = l_Array_mkArray1___redArg(v___x_858_);
v___y_786_ = v___y_828_;
v___y_787_ = v___y_829_;
v___y_788_ = v___y_830_;
v___y_789_ = v___y_832_;
v___y_790_ = v___y_833_;
v___y_791_ = v___y_834_;
v___y_792_ = v___y_835_;
v___y_793_ = v___y_836_;
v___y_794_ = v___y_837_;
v___y_795_ = v___y_838_;
v___y_796_ = v___y_839_;
v___y_797_ = v___x_848_;
v___y_798_ = v___y_843_;
v___y_799_ = v___y_841_;
v___y_800_ = v___y_842_;
v___y_801_ = v___y_840_;
v___y_802_ = v___y_844_;
v___y_803_ = v___y_845_;
v___y_804_ = v___x_859_;
goto v___jp_785_;
}
else
{
lean_object* v___x_860_; 
lean_dec(v___y_831_);
v___x_860_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_786_ = v___y_828_;
v___y_787_ = v___y_829_;
v___y_788_ = v___y_830_;
v___y_789_ = v___y_832_;
v___y_790_ = v___y_833_;
v___y_791_ = v___y_834_;
v___y_792_ = v___y_835_;
v___y_793_ = v___y_836_;
v___y_794_ = v___y_837_;
v___y_795_ = v___y_838_;
v___y_796_ = v___y_839_;
v___y_797_ = v___x_848_;
v___y_798_ = v___y_843_;
v___y_799_ = v___y_841_;
v___y_800_ = v___y_842_;
v___y_801_ = v___y_840_;
v___y_802_ = v___y_844_;
v___y_803_ = v___y_845_;
v___y_804_ = v___x_860_;
goto v___jp_785_;
}
}
v___jp_861_:
{
lean_object* v___x_874_; 
lean_inc(v___y_866_);
v___x_874_ = l_Lean_evalPrec(v___y_866_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_a_876_; lean_object* v_quotContext_877_; lean_object* v_currMacroScope_878_; lean_object* v_ref_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
v_a_876_ = lean_ctor_get(v___x_874_, 1);
lean_inc(v_a_876_);
lean_dec_ref(v___x_874_);
v_quotContext_877_ = lean_ctor_get(v___y_872_, 1);
v_currMacroScope_878_ = lean_ctor_get(v___y_872_, 2);
v_ref_879_ = lean_ctor_get(v___y_872_, 5);
v___x_880_ = lean_unsigned_to_nat(7u);
v___x_881_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_880_);
v___x_882_ = lean_unsigned_to_nat(9u);
v___x_883_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_882_);
lean_dec(v_stx_152_);
v___x_884_ = lean_nat_add(v_a_875_, v___y_865_);
lean_dec(v_a_875_);
v___x_885_ = l_Nat_reprFast(v___x_884_);
v___x_886_ = lean_box(2);
v___x_887_ = l_Lean_Syntax_mkNumLit(v___x_885_, v___x_886_);
v___x_888_ = l_Lean_SourceInfo_fromRef(v_ref_879_, v___y_868_);
v___x_889_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_890_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_891_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_892_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_870_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_894_; 
v_val_893_ = lean_ctor_get(v___y_870_, 0);
lean_inc(v_val_893_);
lean_dec_ref(v___y_870_);
v___x_894_ = l_Array_mkArray1___redArg(v_val_893_);
v___y_828_ = v_quotContext_877_;
v___y_829_ = v_currMacroScope_878_;
v___y_830_ = v___x_889_;
v___y_831_ = v___y_869_;
v___y_832_ = v___x_887_;
v___y_833_ = v___y_862_;
v___y_834_ = v___y_863_;
v___y_835_ = v___x_881_;
v___y_836_ = v___x_892_;
v___y_837_ = v___x_888_;
v___y_838_ = v___y_864_;
v___y_839_ = v___x_890_;
v___y_840_ = v___y_866_;
v___y_841_ = v_prio_871_;
v___y_842_ = v___x_891_;
v___y_843_ = v___x_883_;
v___y_844_ = v___y_867_;
v___y_845_ = v_a_876_;
v___y_846_ = v___x_894_;
goto v___jp_827_;
}
else
{
lean_object* v___x_895_; 
lean_dec(v___y_870_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_828_ = v_quotContext_877_;
v___y_829_ = v_currMacroScope_878_;
v___y_830_ = v___x_889_;
v___y_831_ = v___y_869_;
v___y_832_ = v___x_887_;
v___y_833_ = v___y_862_;
v___y_834_ = v___y_863_;
v___y_835_ = v___x_881_;
v___y_836_ = v___x_892_;
v___y_837_ = v___x_888_;
v___y_838_ = v___y_864_;
v___y_839_ = v___x_890_;
v___y_840_ = v___y_866_;
v___y_841_ = v_prio_871_;
v___y_842_ = v___x_891_;
v___y_843_ = v___x_883_;
v___y_844_ = v___y_867_;
v___y_845_ = v_a_876_;
v___y_846_ = v___x_895_;
goto v___jp_827_;
}
}
else
{
lean_object* v_a_896_; lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_prio_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v___y_867_);
lean_dec(v___y_866_);
lean_dec(v_stx_152_);
v_a_896_ = lean_ctor_get(v___x_874_, 0);
v_a_897_ = lean_ctor_get(v___x_874_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_874_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_inc(v_a_896_);
lean_dec(v___x_874_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_896_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
v___jp_905_:
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_unsigned_to_nat(6u);
v___x_919_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_918_);
v___x_920_ = l_Lean_Syntax_isNone(v___x_919_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
lean_inc(v___x_919_);
v___x_921_ = l_Lean_Syntax_matchesNull(v___x_919_, v___y_910_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_dec(v___x_919_);
lean_dec(v_name_915_);
lean_dec(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_911_);
lean_dec(v_stx_152_);
v___x_922_ = l_Lean_Macro_throwUnsupported___redArg(v___y_917_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = l_Lean_Syntax_getArg(v___x_919_, v___x_430_);
lean_dec(v___x_919_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_923_);
v___x_925_ = l_Lean_Syntax_isOfKind(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec(v___x_923_);
lean_dec(v_name_915_);
lean_dec(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_911_);
lean_dec(v_stx_152_);
v___x_926_ = l_Lean_Macro_throwUnsupported___redArg(v___y_917_);
return v___x_926_;
}
else
{
lean_object* v_prio_927_; lean_object* v___x_928_; 
v_prio_927_ = l_Lean_Syntax_getArg(v___x_923_, v___y_906_);
lean_dec(v___x_923_);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v_prio_927_);
v___y_862_ = v___y_907_;
v___y_863_ = v___y_908_;
v___y_864_ = v___y_909_;
v___y_865_ = v___y_910_;
v___y_866_ = v___y_911_;
v___y_867_ = v_name_915_;
v___y_868_ = v___y_912_;
v___y_869_ = v___y_913_;
v___y_870_ = v___y_914_;
v_prio_871_ = v___x_928_;
v___y_872_ = v___y_916_;
v___y_873_ = v___y_917_;
goto v___jp_861_;
}
}
}
else
{
lean_object* v___x_929_; 
lean_dec(v___x_919_);
v___x_929_ = lean_box(0);
v___y_862_ = v___y_907_;
v___y_863_ = v___y_908_;
v___y_864_ = v___y_909_;
v___y_865_ = v___y_910_;
v___y_866_ = v___y_911_;
v___y_867_ = v_name_915_;
v___y_868_ = v___y_912_;
v___y_869_ = v___y_913_;
v___y_870_ = v___y_914_;
v_prio_871_ = v___x_929_;
v___y_872_ = v___y_916_;
v___y_873_ = v___y_917_;
goto v___jp_861_;
}
}
v___jp_930_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_inc_ref(v___y_936_);
v___x_951_ = l_Array_append___redArg(v___y_936_, v___y_950_);
lean_dec_ref(v___y_950_);
lean_inc(v___y_946_);
lean_inc(v___y_943_);
v___x_952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_952_, 0, v___y_943_);
lean_ctor_set(v___x_952_, 1, v___y_946_);
lean_ctor_set(v___x_952_, 2, v___x_951_);
if (lean_obj_tag(v___y_948_) == 1)
{
lean_object* v_val_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_val_953_ = lean_ctor_get(v___y_948_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v___y_948_);
v___x_954_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_955_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_943_, 5);
v___x_956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_956_, 0, v___y_943_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___y_943_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v___y_943_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_962_, 0, v___y_943_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_Syntax_node5(v___y_943_, v___x_954_, v___x_956_, v___x_958_, v___x_960_, v_val_953_, v___x_962_);
v___x_964_ = l_Array_mkArray1___redArg(v___x_963_);
v___y_312_ = v___y_931_;
v___y_313_ = v___y_932_;
v___y_314_ = v___y_933_;
v___y_315_ = v___y_934_;
v___y_316_ = v___y_935_;
v___y_317_ = v___y_936_;
v___y_318_ = v___y_937_;
v___y_319_ = v___y_938_;
v___y_320_ = v___y_939_;
v___y_321_ = v___y_941_;
v___y_322_ = v___y_942_;
v___y_323_ = v___y_940_;
v___y_324_ = v___y_943_;
v___y_325_ = v___y_945_;
v___y_326_ = v___y_944_;
v___y_327_ = v___y_946_;
v___y_328_ = v___y_947_;
v___y_329_ = v___x_952_;
v___y_330_ = v___y_949_;
v___y_331_ = v___x_964_;
goto v___jp_311_;
}
else
{
lean_object* v___x_965_; 
lean_dec(v___y_948_);
v___x_965_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_312_ = v___y_931_;
v___y_313_ = v___y_932_;
v___y_314_ = v___y_933_;
v___y_315_ = v___y_934_;
v___y_316_ = v___y_935_;
v___y_317_ = v___y_936_;
v___y_318_ = v___y_937_;
v___y_319_ = v___y_938_;
v___y_320_ = v___y_939_;
v___y_321_ = v___y_941_;
v___y_322_ = v___y_942_;
v___y_323_ = v___y_940_;
v___y_324_ = v___y_943_;
v___y_325_ = v___y_945_;
v___y_326_ = v___y_944_;
v___y_327_ = v___y_946_;
v___y_328_ = v___y_947_;
v___y_329_ = v___x_952_;
v___y_330_ = v___y_949_;
v___y_331_ = v___x_965_;
goto v___jp_311_;
}
}
v___jp_966_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_inc_ref_n(v___y_972_, 2);
v___x_986_ = l_Array_append___redArg(v___y_972_, v___y_985_);
lean_dec_ref(v___y_985_);
lean_inc_n(v___y_980_, 3);
lean_inc_n(v___y_977_, 7);
v___x_987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_987_, 0, v___y_977_);
lean_ctor_set(v___x_987_, 1, v___y_980_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
v___x_988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_988_, 0, v___y_977_);
lean_ctor_set(v___x_988_, 1, v___y_980_);
lean_ctor_set(v___x_988_, 2, v___y_972_);
lean_inc(v___y_978_);
v___x_989_ = l_Lean_Syntax_node1(v___y_977_, v___y_978_, v___x_988_);
lean_inc_ref(v___y_967_);
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___y_977_);
lean_ctor_set(v___x_990_, 1, v___y_967_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_977_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_inc_ref(v___x_992_);
lean_inc(v___y_981_);
v___x_993_ = l_Lean_Syntax_node2(v___y_977_, v___y_981_, v___x_992_, v___y_984_);
v___x_994_ = l_Lean_Syntax_node1(v___y_977_, v___y_980_, v___x_993_);
if (lean_obj_tag(v___y_970_) == 1)
{
lean_object* v_val_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_val_995_ = lean_ctor_get(v___y_970_, 0);
lean_inc(v_val_995_);
lean_dec_ref(v___y_970_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_997_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_977_, 5);
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___y_977_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___y_977_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_977_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___y_977_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node5(v___y_977_, v___x_996_, v___x_998_, v___x_1000_, v___x_1002_, v_val_995_, v___x_1004_);
v___x_1006_ = l_Array_mkArray1___redArg(v___x_1005_);
v___y_931_ = v___y_968_;
v___y_932_ = v___y_969_;
v___y_933_ = v___y_971_;
v___y_934_ = v___x_992_;
v___y_935_ = v___x_989_;
v___y_936_ = v___y_972_;
v___y_937_ = v___x_994_;
v___y_938_ = v___y_973_;
v___y_939_ = v___y_974_;
v___y_940_ = v___y_976_;
v___y_941_ = v___y_975_;
v___y_942_ = v___x_990_;
v___y_943_ = v___y_977_;
v___y_944_ = v___x_987_;
v___y_945_ = v___y_979_;
v___y_946_ = v___y_980_;
v___y_947_ = v___y_981_;
v___y_948_ = v___y_983_;
v___y_949_ = v___y_982_;
v___y_950_ = v___x_1006_;
goto v___jp_930_;
}
else
{
lean_object* v___x_1007_; 
lean_dec(v___y_970_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_931_ = v___y_968_;
v___y_932_ = v___y_969_;
v___y_933_ = v___y_971_;
v___y_934_ = v___x_992_;
v___y_935_ = v___x_989_;
v___y_936_ = v___y_972_;
v___y_937_ = v___x_994_;
v___y_938_ = v___y_973_;
v___y_939_ = v___y_974_;
v___y_940_ = v___y_976_;
v___y_941_ = v___y_975_;
v___y_942_ = v___x_990_;
v___y_943_ = v___y_977_;
v___y_944_ = v___x_987_;
v___y_945_ = v___y_979_;
v___y_946_ = v___y_980_;
v___y_947_ = v___y_981_;
v___y_948_ = v___y_983_;
v___y_949_ = v___y_982_;
v___y_950_ = v___x_1007_;
goto v___jp_930_;
}
}
v___jp_1008_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_inc_ref(v___y_1014_);
v___x_1028_ = l_Array_append___redArg(v___y_1014_, v___y_1027_);
lean_dec_ref(v___y_1027_);
lean_inc(v___y_1022_);
lean_inc(v___y_1019_);
v___x_1029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1029_, 0, v___y_1019_);
lean_ctor_set(v___x_1029_, 1, v___y_1022_);
lean_ctor_set(v___x_1029_, 2, v___x_1028_);
if (lean_obj_tag(v___y_1016_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_val_1030_ = lean_ctor_get(v___y_1016_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v___y_1016_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_1021_);
v___x_1032_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_1021_, v___x_1031_);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_n(v___y_1019_, 4);
v___x_1034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___y_1019_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
lean_inc_ref(v___y_1014_);
v___x_1035_ = l_Array_append___redArg(v___y_1014_, v_val_1030_);
lean_dec(v_val_1030_);
lean_inc(v___y_1022_);
v___x_1036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1036_, 0, v___y_1019_);
lean_ctor_set(v___x_1036_, 1, v___y_1022_);
lean_ctor_set(v___x_1036_, 2, v___x_1035_);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
v___x_1038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___y_1019_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_Syntax_node3(v___y_1019_, v___x_1032_, v___x_1034_, v___x_1036_, v___x_1038_);
v___x_1040_ = l_Array_mkArray1___redArg(v___x_1039_);
v___y_967_ = v___y_1009_;
v___y_968_ = v___y_1010_;
v___y_969_ = v___y_1011_;
v___y_970_ = v___y_1012_;
v___y_971_ = v___y_1013_;
v___y_972_ = v___y_1014_;
v___y_973_ = v___y_1015_;
v___y_974_ = v___x_1029_;
v___y_975_ = v___y_1017_;
v___y_976_ = v___y_1018_;
v___y_977_ = v___y_1019_;
v___y_978_ = v___y_1020_;
v___y_979_ = v___y_1021_;
v___y_980_ = v___y_1022_;
v___y_981_ = v___y_1023_;
v___y_982_ = v___y_1025_;
v___y_983_ = v___y_1024_;
v___y_984_ = v___y_1026_;
v___y_985_ = v___x_1040_;
goto v___jp_966_;
}
else
{
lean_object* v___x_1041_; 
lean_dec(v___y_1016_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_967_ = v___y_1009_;
v___y_968_ = v___y_1010_;
v___y_969_ = v___y_1011_;
v___y_970_ = v___y_1012_;
v___y_971_ = v___y_1013_;
v___y_972_ = v___y_1014_;
v___y_973_ = v___y_1015_;
v___y_974_ = v___x_1029_;
v___y_975_ = v___y_1017_;
v___y_976_ = v___y_1018_;
v___y_977_ = v___y_1019_;
v___y_978_ = v___y_1020_;
v___y_979_ = v___y_1021_;
v___y_980_ = v___y_1022_;
v___y_981_ = v___y_1023_;
v___y_982_ = v___y_1025_;
v___y_983_ = v___y_1024_;
v___y_984_ = v___y_1026_;
v___y_985_ = v___x_1041_;
goto v___jp_966_;
}
}
v___jp_1042_:
{
lean_object* v___x_1055_; 
lean_inc(v___y_1051_);
v___x_1055_ = l_Lean_evalPrec(v___y_1051_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v_a_1057_; lean_object* v_quotContext_1058_; lean_object* v_currMacroScope_1059_; lean_object* v_ref_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
v_a_1057_ = lean_ctor_get(v___x_1055_, 1);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1055_);
v_quotContext_1058_ = lean_ctor_get(v___y_1053_, 1);
v_currMacroScope_1059_ = lean_ctor_get(v___y_1053_, 2);
v_ref_1060_ = lean_ctor_get(v___y_1053_, 5);
v___x_1061_ = lean_unsigned_to_nat(7u);
v___x_1062_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1061_);
v___x_1063_ = lean_unsigned_to_nat(9u);
v___x_1064_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1063_);
lean_dec(v_stx_152_);
v___x_1065_ = lean_nat_add(v_a_1056_, v___y_1047_);
lean_dec(v_a_1056_);
v___x_1066_ = l_Nat_reprFast(v___x_1065_);
v___x_1067_ = lean_box(2);
v___x_1068_ = l_Lean_Syntax_mkNumLit(v___x_1066_, v___x_1067_);
v___x_1069_ = l_Lean_SourceInfo_fromRef(v_ref_1060_, v___y_1046_);
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_1073_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_1050_) == 1)
{
lean_object* v_val_1074_; lean_object* v___x_1075_; 
v_val_1074_ = lean_ctor_get(v___y_1050_, 0);
lean_inc(v_val_1074_);
lean_dec_ref(v___y_1050_);
v___x_1075_ = l_Array_mkArray1___redArg(v_val_1074_);
v___y_1009_ = v___x_1070_;
v___y_1010_ = v_currMacroScope_1059_;
v___y_1011_ = v___x_1064_;
v___y_1012_ = v___y_1044_;
v___y_1013_ = v_a_1057_;
v___y_1014_ = v___x_1073_;
v___y_1015_ = v___x_1062_;
v___y_1016_ = v___y_1049_;
v___y_1017_ = v___x_1071_;
v___y_1018_ = v_quotContext_1058_;
v___y_1019_ = v___x_1069_;
v___y_1020_ = v___y_1043_;
v___y_1021_ = v___y_1045_;
v___y_1022_ = v___x_1072_;
v___y_1023_ = v___y_1048_;
v___y_1024_ = v_prio_1052_;
v___y_1025_ = v___x_1068_;
v___y_1026_ = v___y_1051_;
v___y_1027_ = v___x_1075_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1076_; 
lean_dec(v___y_1050_);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1009_ = v___x_1070_;
v___y_1010_ = v_currMacroScope_1059_;
v___y_1011_ = v___x_1064_;
v___y_1012_ = v___y_1044_;
v___y_1013_ = v_a_1057_;
v___y_1014_ = v___x_1073_;
v___y_1015_ = v___x_1062_;
v___y_1016_ = v___y_1049_;
v___y_1017_ = v___x_1071_;
v___y_1018_ = v_quotContext_1058_;
v___y_1019_ = v___x_1069_;
v___y_1020_ = v___y_1043_;
v___y_1021_ = v___y_1045_;
v___y_1022_ = v___x_1072_;
v___y_1023_ = v___y_1048_;
v___y_1024_ = v_prio_1052_;
v___y_1025_ = v___x_1068_;
v___y_1026_ = v___y_1051_;
v___y_1027_ = v___x_1076_;
goto v___jp_1008_;
}
}
else
{
lean_object* v_a_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_prio_1052_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec(v___y_1044_);
lean_dec(v_stx_152_);
v_a_1077_ = lean_ctor_get(v___x_1055_, 0);
v_a_1078_ = lean_ctor_get(v___x_1055_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1055_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_inc(v_a_1077_);
lean_dec(v___x_1055_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
v___jp_1086_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_unsigned_to_nat(6u);
v___x_1100_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1099_);
v___x_1101_ = l_Lean_Syntax_isNone(v___x_1100_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; 
lean_inc(v___x_1100_);
v___x_1102_ = l_Lean_Syntax_matchesNull(v___x_1100_, v___y_1091_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
lean_dec(v___x_1100_);
lean_dec(v_name_1096_);
lean_dec(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec(v_stx_152_);
v___x_1103_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1098_);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = l_Lean_Syntax_getArg(v___x_1100_, v___x_430_);
lean_dec(v___x_1100_);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_1104_);
v___x_1106_ = l_Lean_Syntax_isOfKind(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_dec(v___x_1104_);
lean_dec(v_name_1096_);
lean_dec(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec(v_stx_152_);
v___x_1107_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1098_);
return v___x_1107_;
}
else
{
lean_object* v_prio_1108_; lean_object* v___x_1109_; 
v_prio_1108_ = l_Lean_Syntax_getArg(v___x_1104_, v___y_1087_);
lean_dec(v___x_1104_);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_prio_1108_);
v___y_1043_ = v___y_1088_;
v___y_1044_ = v_name_1096_;
v___y_1045_ = v___y_1089_;
v___y_1046_ = v___y_1090_;
v___y_1047_ = v___y_1091_;
v___y_1048_ = v___y_1092_;
v___y_1049_ = v___y_1093_;
v___y_1050_ = v___y_1094_;
v___y_1051_ = v___y_1095_;
v_prio_1052_ = v___x_1109_;
v___y_1053_ = v___y_1097_;
v___y_1054_ = v___y_1098_;
goto v___jp_1042_;
}
}
}
else
{
lean_object* v___x_1110_; 
lean_dec(v___x_1100_);
v___x_1110_ = lean_box(0);
v___y_1043_ = v___y_1088_;
v___y_1044_ = v_name_1096_;
v___y_1045_ = v___y_1089_;
v___y_1046_ = v___y_1090_;
v___y_1047_ = v___y_1091_;
v___y_1048_ = v___y_1092_;
v___y_1049_ = v___y_1093_;
v___y_1050_ = v___y_1094_;
v___y_1051_ = v___y_1095_;
v_prio_1052_ = v___x_1110_;
v___y_1053_ = v___y_1097_;
v___y_1054_ = v___y_1098_;
goto v___jp_1042_;
}
}
v___jp_1111_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_inc_ref(v___y_1113_);
v___x_1132_ = l_Array_append___redArg(v___y_1113_, v___y_1131_);
lean_dec_ref(v___y_1131_);
lean_inc(v___y_1125_);
lean_inc(v___y_1123_);
v___x_1133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1133_, 0, v___y_1123_);
lean_ctor_set(v___x_1133_, 1, v___y_1125_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
if (lean_obj_tag(v___y_1116_) == 1)
{
lean_object* v_val_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_val_1134_ = lean_ctor_get(v___y_1116_, 0);
lean_inc(v_val_1134_);
lean_dec_ref(v___y_1116_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_1123_, 5);
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1123_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1123_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_1141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___y_1123_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_1143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___y_1123_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_Syntax_node5(v___y_1123_, v___x_1135_, v___x_1137_, v___x_1139_, v___x_1141_, v_val_1134_, v___x_1143_);
v___x_1145_ = l_Array_mkArray1___redArg(v___x_1144_);
v___y_370_ = v___y_1112_;
v___y_371_ = v___y_1113_;
v___y_372_ = v___y_1114_;
v___y_373_ = v___y_1115_;
v___y_374_ = v___y_1117_;
v___y_375_ = v___y_1118_;
v___y_376_ = v___y_1119_;
v___y_377_ = v___y_1120_;
v___y_378_ = v___y_1121_;
v___y_379_ = v___y_1122_;
v___y_380_ = v___y_1124_;
v___y_381_ = v___y_1123_;
v___y_382_ = v___y_1125_;
v___y_383_ = v___y_1126_;
v___y_384_ = v___x_1133_;
v___y_385_ = v___y_1127_;
v___y_386_ = v___y_1129_;
v___y_387_ = v___y_1128_;
v___y_388_ = v___y_1130_;
v___y_389_ = v___x_1145_;
goto v___jp_369_;
}
else
{
lean_object* v___x_1146_; 
lean_dec(v___y_1116_);
v___x_1146_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_370_ = v___y_1112_;
v___y_371_ = v___y_1113_;
v___y_372_ = v___y_1114_;
v___y_373_ = v___y_1115_;
v___y_374_ = v___y_1117_;
v___y_375_ = v___y_1118_;
v___y_376_ = v___y_1119_;
v___y_377_ = v___y_1120_;
v___y_378_ = v___y_1121_;
v___y_379_ = v___y_1122_;
v___y_380_ = v___y_1124_;
v___y_381_ = v___y_1123_;
v___y_382_ = v___y_1125_;
v___y_383_ = v___y_1126_;
v___y_384_ = v___x_1133_;
v___y_385_ = v___y_1127_;
v___y_386_ = v___y_1129_;
v___y_387_ = v___y_1128_;
v___y_388_ = v___y_1130_;
v___y_389_ = v___x_1146_;
goto v___jp_369_;
}
}
v___jp_1147_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_inc_ref_n(v___y_1149_, 2);
v___x_1167_ = l_Array_append___redArg(v___y_1149_, v___y_1166_);
lean_dec_ref(v___y_1166_);
lean_inc_n(v___y_1161_, 3);
lean_inc_n(v___y_1160_, 7);
v___x_1168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1168_, 0, v___y_1160_);
lean_ctor_set(v___x_1168_, 1, v___y_1161_);
lean_ctor_set(v___x_1168_, 2, v___x_1167_);
v___x_1169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1169_, 0, v___y_1160_);
lean_ctor_set(v___x_1169_, 1, v___y_1161_);
lean_ctor_set(v___x_1169_, 2, v___y_1149_);
lean_inc(v___y_1156_);
v___x_1170_ = l_Lean_Syntax_node1(v___y_1160_, v___y_1156_, v___x_1169_);
lean_inc_ref(v___y_1150_);
v___x_1171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___y_1160_);
lean_ctor_set(v___x_1171_, 1, v___y_1150_);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
v___x_1173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___y_1160_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
lean_inc_ref(v___x_1173_);
lean_inc(v___y_1162_);
v___x_1174_ = l_Lean_Syntax_node2(v___y_1160_, v___y_1162_, v___x_1173_, v___y_1164_);
v___x_1175_ = l_Lean_Syntax_node1(v___y_1160_, v___y_1161_, v___x_1174_);
if (lean_obj_tag(v___y_1153_) == 1)
{
lean_object* v_val_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_val_1176_ = lean_ctor_get(v___y_1153_, 0);
lean_inc(v_val_1176_);
lean_dec_ref(v___y_1153_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc_n(v___y_1160_, 5);
v___x_1179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1160_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
v___x_1181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___y_1160_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
v___x_1183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___y_1160_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
v___x_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___y_1160_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_node5(v___y_1160_, v___x_1177_, v___x_1179_, v___x_1181_, v___x_1183_, v_val_1176_, v___x_1185_);
v___x_1187_ = l_Array_mkArray1___redArg(v___x_1186_);
v___y_1112_ = v___y_1148_;
v___y_1113_ = v___y_1149_;
v___y_1114_ = v___x_1171_;
v___y_1115_ = v___x_1170_;
v___y_1116_ = v___y_1151_;
v___y_1117_ = v___y_1152_;
v___y_1118_ = v___y_1154_;
v___y_1119_ = v___x_1168_;
v___y_1120_ = v___y_1155_;
v___y_1121_ = v___y_1157_;
v___y_1122_ = v___y_1158_;
v___y_1123_ = v___y_1160_;
v___y_1124_ = v___y_1159_;
v___y_1125_ = v___y_1161_;
v___y_1126_ = v___y_1162_;
v___y_1127_ = v___y_1163_;
v___y_1128_ = v___x_1173_;
v___y_1129_ = v___x_1175_;
v___y_1130_ = v___y_1165_;
v___y_1131_ = v___x_1187_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1188_; 
lean_dec(v___y_1153_);
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1112_ = v___y_1148_;
v___y_1113_ = v___y_1149_;
v___y_1114_ = v___x_1171_;
v___y_1115_ = v___x_1170_;
v___y_1116_ = v___y_1151_;
v___y_1117_ = v___y_1152_;
v___y_1118_ = v___y_1154_;
v___y_1119_ = v___x_1168_;
v___y_1120_ = v___y_1155_;
v___y_1121_ = v___y_1157_;
v___y_1122_ = v___y_1158_;
v___y_1123_ = v___y_1160_;
v___y_1124_ = v___y_1159_;
v___y_1125_ = v___y_1161_;
v___y_1126_ = v___y_1162_;
v___y_1127_ = v___y_1163_;
v___y_1128_ = v___x_1173_;
v___y_1129_ = v___x_1175_;
v___y_1130_ = v___y_1165_;
v___y_1131_ = v___x_1188_;
goto v___jp_1111_;
}
}
v___jp_1189_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_inc_ref(v___y_1191_);
v___x_1209_ = l_Array_append___redArg(v___y_1191_, v___y_1208_);
lean_dec_ref(v___y_1208_);
lean_inc(v___y_1203_);
lean_inc(v___y_1201_);
v___x_1210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1210_, 0, v___y_1201_);
lean_ctor_set(v___x_1210_, 1, v___y_1203_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
if (lean_obj_tag(v___y_1197_) == 1)
{
lean_object* v_val_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_val_1211_ = lean_ctor_get(v___y_1197_, 0);
lean_inc(v_val_1211_);
lean_dec_ref(v___y_1197_);
v___x_1212_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(v___y_1200_);
v___x_1213_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_1200_, v___x_1212_);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_n(v___y_1201_, 4);
v___x_1215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___y_1201_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
lean_inc_ref(v___y_1191_);
v___x_1216_ = l_Array_append___redArg(v___y_1191_, v_val_1211_);
lean_dec(v_val_1211_);
lean_inc(v___y_1203_);
v___x_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1201_);
lean_ctor_set(v___x_1217_, 1, v___y_1203_);
lean_ctor_set(v___x_1217_, 2, v___x_1216_);
v___x_1218_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
v___x_1219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___y_1201_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_Syntax_node3(v___y_1201_, v___x_1213_, v___x_1215_, v___x_1217_, v___x_1219_);
v___x_1221_ = l_Array_mkArray1___redArg(v___x_1220_);
v___y_1148_ = v___y_1190_;
v___y_1149_ = v___y_1191_;
v___y_1150_ = v___y_1192_;
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1194_;
v___y_1153_ = v___y_1195_;
v___y_1154_ = v___y_1196_;
v___y_1155_ = v___y_1198_;
v___y_1156_ = v___y_1199_;
v___y_1157_ = v___x_1210_;
v___y_1158_ = v___y_1200_;
v___y_1159_ = v___y_1202_;
v___y_1160_ = v___y_1201_;
v___y_1161_ = v___y_1203_;
v___y_1162_ = v___y_1204_;
v___y_1163_ = v___y_1205_;
v___y_1164_ = v___y_1206_;
v___y_1165_ = v___y_1207_;
v___y_1166_ = v___x_1221_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1222_; 
lean_dec(v___y_1197_);
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1148_ = v___y_1190_;
v___y_1149_ = v___y_1191_;
v___y_1150_ = v___y_1192_;
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1194_;
v___y_1153_ = v___y_1195_;
v___y_1154_ = v___y_1196_;
v___y_1155_ = v___y_1198_;
v___y_1156_ = v___y_1199_;
v___y_1157_ = v___x_1210_;
v___y_1158_ = v___y_1200_;
v___y_1159_ = v___y_1202_;
v___y_1160_ = v___y_1201_;
v___y_1161_ = v___y_1203_;
v___y_1162_ = v___y_1204_;
v___y_1163_ = v___y_1205_;
v___y_1164_ = v___y_1206_;
v___y_1165_ = v___y_1207_;
v___y_1166_ = v___x_1222_;
goto v___jp_1147_;
}
}
v___jp_1223_:
{
lean_object* v___x_1235_; 
lean_inc(v___y_1231_);
v___x_1235_ = l_Lean_evalPrec(v___y_1231_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v_a_1237_; lean_object* v_quotContext_1238_; lean_object* v_currMacroScope_1239_; lean_object* v_ref_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
v_a_1237_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1235_);
v_quotContext_1238_ = lean_ctor_get(v___y_1233_, 1);
v_currMacroScope_1239_ = lean_ctor_get(v___y_1233_, 2);
v_ref_1240_ = lean_ctor_get(v___y_1233_, 5);
v___x_1241_ = lean_unsigned_to_nat(7u);
v___x_1242_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1241_);
v___x_1243_ = lean_unsigned_to_nat(9u);
v___x_1244_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1243_);
lean_dec(v_stx_152_);
v___x_1245_ = lean_nat_add(v_a_1236_, v___y_1227_);
lean_dec(v_a_1236_);
v___x_1246_ = l_Nat_reprFast(v___x_1245_);
v___x_1247_ = lean_box(2);
v___x_1248_ = l_Lean_Syntax_mkNumLit(v___x_1246_, v___x_1247_);
v___x_1249_ = 0;
v___x_1250_ = l_Lean_SourceInfo_fromRef(v_ref_1240_, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
v___x_1253_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
v___x_1254_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(v___y_1230_) == 1)
{
lean_object* v_val_1255_; lean_object* v___x_1256_; 
v_val_1255_ = lean_ctor_get(v___y_1230_, 0);
lean_inc(v_val_1255_);
lean_dec_ref(v___y_1230_);
v___x_1256_ = l_Array_mkArray1___redArg(v_val_1255_);
v___y_1190_ = v_currMacroScope_1239_;
v___y_1191_ = v___x_1254_;
v___y_1192_ = v___x_1251_;
v___y_1193_ = v_prio_1232_;
v___y_1194_ = v___x_1252_;
v___y_1195_ = v___y_1226_;
v___y_1196_ = v_quotContext_1238_;
v___y_1197_ = v___y_1229_;
v___y_1198_ = v___x_1242_;
v___y_1199_ = v___y_1224_;
v___y_1200_ = v___y_1225_;
v___y_1201_ = v___x_1250_;
v___y_1202_ = v_a_1237_;
v___y_1203_ = v___x_1253_;
v___y_1204_ = v___y_1228_;
v___y_1205_ = v___x_1248_;
v___y_1206_ = v___y_1231_;
v___y_1207_ = v___x_1244_;
v___y_1208_ = v___x_1256_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1257_; 
lean_dec(v___y_1230_);
v___x_1257_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
v___y_1190_ = v_currMacroScope_1239_;
v___y_1191_ = v___x_1254_;
v___y_1192_ = v___x_1251_;
v___y_1193_ = v_prio_1232_;
v___y_1194_ = v___x_1252_;
v___y_1195_ = v___y_1226_;
v___y_1196_ = v_quotContext_1238_;
v___y_1197_ = v___y_1229_;
v___y_1198_ = v___x_1242_;
v___y_1199_ = v___y_1224_;
v___y_1200_ = v___y_1225_;
v___y_1201_ = v___x_1250_;
v___y_1202_ = v_a_1237_;
v___y_1203_ = v___x_1253_;
v___y_1204_ = v___y_1228_;
v___y_1205_ = v___x_1248_;
v___y_1206_ = v___y_1231_;
v___y_1207_ = v___x_1244_;
v___y_1208_ = v___x_1257_;
goto v___jp_1189_;
}
}
else
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_prio_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1226_);
lean_dec(v_stx_152_);
v_a_1258_ = lean_ctor_get(v___x_1235_, 0);
v_a_1259_ = lean_ctor_get(v___x_1235_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1235_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_inc(v_a_1258_);
lean_dec(v___x_1235_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1258_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
v___jp_1267_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_unsigned_to_nat(6u);
v___x_1280_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1279_);
v___x_1281_ = l_Lean_Syntax_isNone(v___x_1280_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; 
lean_inc(v___x_1280_);
v___x_1282_ = l_Lean_Syntax_matchesNull(v___x_1280_, v___y_1271_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec(v___x_1280_);
lean_dec(v_name_1276_);
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v_stx_152_);
v___x_1283_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1278_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = l_Lean_Syntax_getArg(v___x_1280_, v___x_430_);
lean_dec(v___x_1280_);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(v___x_1284_);
v___x_1286_ = l_Lean_Syntax_isOfKind(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v___x_1284_);
lean_dec(v_name_1276_);
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v_stx_152_);
v___x_1287_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1278_);
return v___x_1287_;
}
else
{
lean_object* v_prio_1288_; lean_object* v___x_1289_; 
v_prio_1288_ = l_Lean_Syntax_getArg(v___x_1284_, v___y_1268_);
lean_dec(v___x_1284_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_prio_1288_);
v___y_1224_ = v___y_1269_;
v___y_1225_ = v___y_1270_;
v___y_1226_ = v_name_1276_;
v___y_1227_ = v___y_1271_;
v___y_1228_ = v___y_1272_;
v___y_1229_ = v___y_1273_;
v___y_1230_ = v___y_1275_;
v___y_1231_ = v___y_1274_;
v_prio_1232_ = v___x_1289_;
v___y_1233_ = v___y_1277_;
v___y_1234_ = v___y_1278_;
goto v___jp_1223_;
}
}
}
else
{
lean_object* v___x_1290_; 
lean_dec(v___x_1280_);
v___x_1290_ = lean_box(0);
v___y_1224_ = v___y_1269_;
v___y_1225_ = v___y_1270_;
v___y_1226_ = v_name_1276_;
v___y_1227_ = v___y_1271_;
v___y_1228_ = v___y_1272_;
v___y_1229_ = v___y_1273_;
v___y_1230_ = v___y_1275_;
v___y_1231_ = v___y_1274_;
v_prio_1232_ = v___x_1290_;
v___y_1233_ = v___y_1277_;
v___y_1234_ = v___y_1278_;
goto v___jp_1223_;
}
}
v___jp_1291_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1297_ = lean_unsigned_to_nat(2u);
v___x_1298_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1297_);
v___x_1299_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37));
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39));
lean_inc(v___x_1298_);
v___x_1301_ = l_Lean_Syntax_isOfKind(v___x_1298_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec(v___x_1298_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1302_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = l_Lean_Syntax_getArg(v___x_1298_, v___x_430_);
lean_dec(v___x_1298_);
v___x_1304_ = l_Lean_Syntax_matchesNull(v___x_1303_, v___x_430_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1305_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1306_ = lean_unsigned_to_nat(3u);
v___x_1307_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1306_);
v___x_1308_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41));
lean_inc(v___x_1307_);
v___x_1309_ = l_Lean_Syntax_isOfKind(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43));
lean_inc(v___x_1307_);
v___x_1311_ = l_Lean_Syntax_isOfKind(v___x_1307_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45));
lean_inc(v___x_1307_);
v___x_1313_ = l_Lean_Syntax_isOfKind(v___x_1307_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47));
lean_inc(v___x_1307_);
v___x_1315_ = l_Lean_Syntax_isOfKind(v___x_1307_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49));
v___x_1317_ = l_Lean_Syntax_isOfKind(v___x_1307_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1318_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1319_ = lean_unsigned_to_nat(4u);
v___x_1320_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1320_);
v___x_1322_ = l_Lean_Syntax_isOfKind(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
lean_dec(v___x_1320_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1323_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1324_ = l_Lean_Syntax_getArg(v___x_1320_, v___y_1292_);
lean_dec(v___x_1320_);
v___x_1325_ = lean_unsigned_to_nat(5u);
v___x_1326_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1325_);
v___x_1327_ = l_Lean_Syntax_isNone(v___x_1326_);
if (v___x_1327_ == 0)
{
uint8_t v___x_1328_; 
lean_inc(v___x_1326_);
v___x_1328_ = l_Lean_Syntax_matchesNull(v___x_1326_, v___y_1292_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v___x_1326_);
lean_dec(v___x_1324_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1329_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = l_Lean_Syntax_getArg(v___x_1326_, v___x_430_);
lean_dec(v___x_1326_);
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1330_);
v___x_1332_ = l_Lean_Syntax_isOfKind(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec(v___x_1330_);
lean_dec(v___x_1324_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1333_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1333_;
}
else
{
lean_object* v_name_1334_; lean_object* v___x_1335_; 
v_name_1334_ = l_Lean_Syntax_getArg(v___x_1330_, v___x_1306_);
lean_dec(v___x_1330_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_name_1334_);
v___y_566_ = v___x_1306_;
v___y_567_ = v___x_1300_;
v___y_568_ = v___x_1299_;
v___y_569_ = v___x_1324_;
v___y_570_ = v___x_1315_;
v___y_571_ = v___y_1292_;
v___y_572_ = v___x_1321_;
v___y_573_ = v_attrs_x3f_1294_;
v___y_574_ = v___y_1293_;
v_name_575_ = v___x_1335_;
v___y_576_ = v___y_1295_;
v___y_577_ = v___y_1296_;
goto v___jp_565_;
}
}
}
else
{
lean_object* v___x_1336_; 
lean_dec(v___x_1326_);
v___x_1336_ = lean_box(0);
v___y_566_ = v___x_1306_;
v___y_567_ = v___x_1300_;
v___y_568_ = v___x_1299_;
v___y_569_ = v___x_1324_;
v___y_570_ = v___x_1315_;
v___y_571_ = v___y_1292_;
v___y_572_ = v___x_1321_;
v___y_573_ = v_attrs_x3f_1294_;
v___y_574_ = v___y_1293_;
v_name_575_ = v___x_1336_;
v___y_576_ = v___y_1295_;
v___y_577_ = v___y_1296_;
goto v___jp_565_;
}
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
lean_dec(v___x_1307_);
v___x_1337_ = lean_unsigned_to_nat(4u);
v___x_1338_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1337_);
v___x_1339_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1338_);
v___x_1340_ = l_Lean_Syntax_isOfKind(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec(v___x_1338_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1341_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = l_Lean_Syntax_getArg(v___x_1338_, v___y_1292_);
lean_dec(v___x_1338_);
v___x_1343_ = lean_unsigned_to_nat(5u);
v___x_1344_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1343_);
v___x_1345_ = l_Lean_Syntax_isNone(v___x_1344_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; 
lean_inc(v___x_1344_);
v___x_1346_ = l_Lean_Syntax_matchesNull(v___x_1344_, v___y_1292_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec(v___x_1344_);
lean_dec(v___x_1342_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1347_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = l_Lean_Syntax_getArg(v___x_1344_, v___x_430_);
lean_dec(v___x_1344_);
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1348_);
v___x_1350_ = l_Lean_Syntax_isOfKind(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec(v___x_1348_);
lean_dec(v___x_1342_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1351_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1351_;
}
else
{
lean_object* v_name_1352_; lean_object* v___x_1353_; 
v_name_1352_ = l_Lean_Syntax_getArg(v___x_1348_, v___x_1306_);
lean_dec(v___x_1348_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_name_1352_);
v___y_725_ = v___x_1306_;
v___y_726_ = v___x_1313_;
v___y_727_ = v___x_1300_;
v___y_728_ = v___x_1339_;
v___y_729_ = v___x_1299_;
v___y_730_ = v___y_1292_;
v___y_731_ = v___x_1342_;
v___y_732_ = v_attrs_x3f_1294_;
v___y_733_ = v___y_1293_;
v_name_734_ = v___x_1353_;
v___y_735_ = v___y_1295_;
v___y_736_ = v___y_1296_;
goto v___jp_724_;
}
}
}
else
{
lean_object* v___x_1354_; 
lean_dec(v___x_1344_);
v___x_1354_ = lean_box(0);
v___y_725_ = v___x_1306_;
v___y_726_ = v___x_1313_;
v___y_727_ = v___x_1300_;
v___y_728_ = v___x_1339_;
v___y_729_ = v___x_1299_;
v___y_730_ = v___y_1292_;
v___y_731_ = v___x_1342_;
v___y_732_ = v_attrs_x3f_1294_;
v___y_733_ = v___y_1293_;
v_name_734_ = v___x_1354_;
v___y_735_ = v___y_1295_;
v___y_736_ = v___y_1296_;
goto v___jp_724_;
}
}
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
lean_dec(v___x_1307_);
v___x_1355_ = lean_unsigned_to_nat(4u);
v___x_1356_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1355_);
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1356_);
v___x_1358_ = l_Lean_Syntax_isOfKind(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec(v___x_1356_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1359_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1360_ = l_Lean_Syntax_getArg(v___x_1356_, v___y_1292_);
lean_dec(v___x_1356_);
v___x_1361_ = lean_unsigned_to_nat(5u);
v___x_1362_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1361_);
v___x_1363_ = l_Lean_Syntax_isNone(v___x_1362_);
if (v___x_1363_ == 0)
{
uint8_t v___x_1364_; 
lean_inc(v___x_1362_);
v___x_1364_ = l_Lean_Syntax_matchesNull(v___x_1362_, v___y_1292_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec(v___x_1362_);
lean_dec(v___x_1360_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1365_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = l_Lean_Syntax_getArg(v___x_1362_, v___x_430_);
lean_dec(v___x_1362_);
v___x_1367_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1366_);
v___x_1368_ = l_Lean_Syntax_isOfKind(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec(v___x_1366_);
lean_dec(v___x_1360_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1369_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1369_;
}
else
{
lean_object* v_name_1370_; lean_object* v___x_1371_; 
v_name_1370_ = l_Lean_Syntax_getArg(v___x_1366_, v___x_1306_);
lean_dec(v___x_1366_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_name_1370_);
v___y_906_ = v___x_1306_;
v___y_907_ = v___x_1300_;
v___y_908_ = v___x_1357_;
v___y_909_ = v___x_1299_;
v___y_910_ = v___y_1292_;
v___y_911_ = v___x_1360_;
v___y_912_ = v___x_1311_;
v___y_913_ = v_attrs_x3f_1294_;
v___y_914_ = v___y_1293_;
v_name_915_ = v___x_1371_;
v___y_916_ = v___y_1295_;
v___y_917_ = v___y_1296_;
goto v___jp_905_;
}
}
}
else
{
lean_object* v___x_1372_; 
lean_dec(v___x_1362_);
v___x_1372_ = lean_box(0);
v___y_906_ = v___x_1306_;
v___y_907_ = v___x_1300_;
v___y_908_ = v___x_1357_;
v___y_909_ = v___x_1299_;
v___y_910_ = v___y_1292_;
v___y_911_ = v___x_1360_;
v___y_912_ = v___x_1311_;
v___y_913_ = v_attrs_x3f_1294_;
v___y_914_ = v___y_1293_;
v_name_915_ = v___x_1372_;
v___y_916_ = v___y_1295_;
v___y_917_ = v___y_1296_;
goto v___jp_905_;
}
}
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
lean_dec(v___x_1307_);
v___x_1373_ = lean_unsigned_to_nat(4u);
v___x_1374_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1374_);
v___x_1376_ = l_Lean_Syntax_isOfKind(v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec(v___x_1374_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1377_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1378_ = l_Lean_Syntax_getArg(v___x_1374_, v___y_1292_);
lean_dec(v___x_1374_);
v___x_1379_ = lean_unsigned_to_nat(5u);
v___x_1380_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1379_);
v___x_1381_ = l_Lean_Syntax_isNone(v___x_1380_);
if (v___x_1381_ == 0)
{
uint8_t v___x_1382_; 
lean_inc(v___x_1380_);
v___x_1382_ = l_Lean_Syntax_matchesNull(v___x_1380_, v___y_1292_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
lean_dec(v___x_1380_);
lean_dec(v___x_1378_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1383_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = l_Lean_Syntax_getArg(v___x_1380_, v___x_430_);
lean_dec(v___x_1380_);
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1384_);
v___x_1386_ = l_Lean_Syntax_isOfKind(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_dec(v___x_1384_);
lean_dec(v___x_1378_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1387_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1387_;
}
else
{
lean_object* v_name_1388_; lean_object* v___x_1389_; 
v_name_1388_ = l_Lean_Syntax_getArg(v___x_1384_, v___x_1306_);
lean_dec(v___x_1384_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_name_1388_);
v___y_1087_ = v___x_1306_;
v___y_1088_ = v___x_1300_;
v___y_1089_ = v___x_1299_;
v___y_1090_ = v___x_1309_;
v___y_1091_ = v___y_1292_;
v___y_1092_ = v___x_1375_;
v___y_1093_ = v_attrs_x3f_1294_;
v___y_1094_ = v___y_1293_;
v___y_1095_ = v___x_1378_;
v_name_1096_ = v___x_1389_;
v___y_1097_ = v___y_1295_;
v___y_1098_ = v___y_1296_;
goto v___jp_1086_;
}
}
}
else
{
lean_object* v___x_1390_; 
lean_dec(v___x_1380_);
v___x_1390_ = lean_box(0);
v___y_1087_ = v___x_1306_;
v___y_1088_ = v___x_1300_;
v___y_1089_ = v___x_1299_;
v___y_1090_ = v___x_1309_;
v___y_1091_ = v___y_1292_;
v___y_1092_ = v___x_1375_;
v___y_1093_ = v_attrs_x3f_1294_;
v___y_1094_ = v___y_1293_;
v___y_1095_ = v___x_1378_;
v_name_1096_ = v___x_1390_;
v___y_1097_ = v___y_1295_;
v___y_1098_ = v___y_1296_;
goto v___jp_1086_;
}
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
lean_dec(v___x_1307_);
v___x_1391_ = lean_unsigned_to_nat(4u);
v___x_1392_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(v___x_1392_);
v___x_1394_ = l_Lean_Syntax_isOfKind(v___x_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_dec(v___x_1392_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1395_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1396_ = l_Lean_Syntax_getArg(v___x_1392_, v___y_1292_);
lean_dec(v___x_1392_);
v___x_1397_ = lean_unsigned_to_nat(5u);
v___x_1398_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1397_);
v___x_1399_ = l_Lean_Syntax_isNone(v___x_1398_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
lean_inc(v___x_1398_);
v___x_1400_ = l_Lean_Syntax_matchesNull(v___x_1398_, v___y_1292_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v___x_1398_);
lean_dec(v___x_1396_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1401_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1402_ = l_Lean_Syntax_getArg(v___x_1398_, v___x_430_);
lean_dec(v___x_1398_);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(v___x_1402_);
v___x_1404_ = l_Lean_Syntax_isOfKind(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
lean_dec(v___x_1402_);
lean_dec(v___x_1396_);
lean_dec(v_attrs_x3f_1294_);
lean_dec(v___y_1293_);
lean_dec(v_stx_152_);
v___x_1405_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1296_);
return v___x_1405_;
}
else
{
lean_object* v_name_1406_; lean_object* v___x_1407_; 
v_name_1406_ = l_Lean_Syntax_getArg(v___x_1402_, v___x_1306_);
lean_dec(v___x_1402_);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_name_1406_);
v___y_1268_ = v___x_1306_;
v___y_1269_ = v___x_1300_;
v___y_1270_ = v___x_1299_;
v___y_1271_ = v___y_1292_;
v___y_1272_ = v___x_1393_;
v___y_1273_ = v_attrs_x3f_1294_;
v___y_1274_ = v___x_1396_;
v___y_1275_ = v___y_1293_;
v_name_1276_ = v___x_1407_;
v___y_1277_ = v___y_1295_;
v___y_1278_ = v___y_1296_;
goto v___jp_1267_;
}
}
}
else
{
lean_object* v___x_1408_; 
lean_dec(v___x_1398_);
v___x_1408_ = lean_box(0);
v___y_1268_ = v___x_1306_;
v___y_1269_ = v___x_1300_;
v___y_1270_ = v___x_1299_;
v___y_1271_ = v___y_1292_;
v___y_1272_ = v___x_1393_;
v___y_1273_ = v_attrs_x3f_1294_;
v___y_1274_ = v___x_1396_;
v___y_1275_ = v___y_1293_;
v_name_1276_ = v___x_1408_;
v___y_1277_ = v___y_1295_;
v___y_1278_ = v___y_1296_;
goto v___jp_1267_;
}
}
}
}
}
}
v___jp_1409_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = l_Lean_Syntax_getArg(v_stx_152_, v___x_1413_);
v___x_1415_ = l_Lean_Syntax_isNone(v___x_1414_);
if (v___x_1415_ == 0)
{
uint8_t v___x_1416_; 
lean_inc(v___x_1414_);
v___x_1416_ = l_Lean_Syntax_matchesNull(v___x_1414_, v___x_1413_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec(v___x_1414_);
lean_dec(v_doc_x3f_1410_);
lean_dec(v_stx_152_);
v___x_1417_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1412_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = l_Lean_Syntax_getArg(v___x_1414_, v___x_430_);
lean_dec(v___x_1414_);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(v___x_1418_);
v___x_1420_ = l_Lean_Syntax_isOfKind(v___x_1418_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec(v___x_1418_);
lean_dec(v_doc_x3f_1410_);
lean_dec(v_stx_152_);
v___x_1421_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1412_);
return v___x_1421_;
}
else
{
lean_object* v___x_1422_; lean_object* v_attrs_x3f_1423_; lean_object* v___x_1424_; 
v___x_1422_ = l_Lean_Syntax_getArg(v___x_1418_, v___x_1413_);
lean_dec(v___x_1418_);
v_attrs_x3f_1423_ = l_Lean_Syntax_getArgs(v___x_1422_);
lean_dec(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_attrs_x3f_1423_);
v___y_1292_ = v___x_1413_;
v___y_1293_ = v_doc_x3f_1410_;
v_attrs_x3f_1294_ = v___x_1424_;
v___y_1295_ = v___y_1411_;
v___y_1296_ = v___y_1412_;
goto v___jp_1291_;
}
}
}
else
{
lean_object* v___x_1425_; 
lean_dec(v___x_1414_);
v___x_1425_ = lean_box(0);
v___y_1292_ = v___x_1413_;
v___y_1293_ = v_doc_x3f_1410_;
v_attrs_x3f_1294_ = v___x_1425_;
v___y_1295_ = v___y_1411_;
v___y_1296_ = v___y_1412_;
goto v___jp_1291_;
}
}
}
v___jp_157_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc_ref(v___y_158_);
v___x_175_ = l_Array_append___redArg(v___y_158_, v___y_174_);
lean_dec_ref(v___y_174_);
lean_inc_n(v___y_171_, 3);
lean_inc_n(v___y_165_, 7);
v___x_176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_176_, 0, v___y_165_);
lean_ctor_set(v___x_176_, 1, v___y_171_);
lean_ctor_set(v___x_176_, 2, v___x_175_);
v___x_177_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_178_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__6, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6);
v___x_179_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
lean_inc(v___y_162_);
lean_inc(v___y_161_);
v___x_180_ = l_Lean_addMacroScope(v___y_161_, v___x_179_, v___y_162_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_182_, 0, v___y_165_);
lean_ctor_set(v___x_182_, 1, v___x_178_);
lean_ctor_set(v___x_182_, 2, v___x_180_);
lean_ctor_set(v___x_182_, 3, v___x_181_);
lean_inc(v___y_159_);
lean_inc_ref(v___x_182_);
v___x_183_ = l_Lean_Syntax_node2(v___y_165_, v___x_177_, v___x_182_, v___y_159_);
v___x_184_ = l_Lean_Syntax_node2(v___y_165_, v___y_171_, v___x_183_, v___y_173_);
v___x_185_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
v___x_186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_186_, 0, v___y_165_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
lean_inc_ref(v___y_166_);
v___x_188_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_166_, v___x_187_);
v___x_189_ = l_Lean_Syntax_node1(v___y_165_, v___y_171_, v___x_182_);
v___x_190_ = l_Lean_Syntax_node2(v___y_165_, v___x_188_, v___y_160_, v___x_189_);
v___x_191_ = lean_unsigned_to_nat(10u);
v___x_192_ = lean_mk_empty_array_with_capacity(v___x_191_);
v___x_193_ = lean_array_push(v___x_192_, v___y_164_);
v___x_194_ = lean_array_push(v___x_193_, v___y_168_);
v___x_195_ = lean_array_push(v___x_194_, v___y_163_);
v___x_196_ = lean_array_push(v___x_195_, v___y_169_);
v___x_197_ = lean_array_push(v___x_196_, v___y_159_);
v___x_198_ = lean_array_push(v___x_197_, v___y_172_);
v___x_199_ = lean_array_push(v___x_198_, v___x_176_);
v___x_200_ = lean_array_push(v___x_199_, v___x_184_);
v___x_201_ = lean_array_push(v___x_200_, v___x_186_);
v___x_202_ = lean_array_push(v___x_201_, v___x_190_);
lean_inc(v___y_167_);
v___x_203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_203_, 0, v___y_165_);
lean_ctor_set(v___x_203_, 1, v___y_167_);
lean_ctor_set(v___x_203_, 2, v___x_202_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___y_170_);
return v___x_204_;
}
v___jp_205_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_inc_ref(v___y_212_);
v___x_223_ = l_Array_append___redArg(v___y_212_, v___y_222_);
lean_dec_ref(v___y_222_);
lean_inc_n(v___y_220_, 3);
lean_inc_n(v___y_218_, 7);
v___x_224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_224_, 0, v___y_218_);
lean_ctor_set(v___x_224_, 1, v___y_220_);
lean_ctor_set(v___x_224_, 2, v___x_223_);
v___x_225_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_226_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__6, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6);
v___x_227_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
lean_inc(v___y_217_);
lean_inc(v___y_211_);
v___x_228_ = l_Lean_addMacroScope(v___y_211_, v___x_227_, v___y_217_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_230_, 0, v___y_218_);
lean_ctor_set(v___x_230_, 1, v___x_226_);
lean_ctor_set(v___x_230_, 2, v___x_228_);
lean_ctor_set(v___x_230_, 3, v___x_229_);
lean_inc(v___y_207_);
lean_inc_ref(v___x_230_);
v___x_231_ = l_Lean_Syntax_node2(v___y_218_, v___x_225_, v___x_230_, v___y_207_);
v___x_232_ = l_Lean_Syntax_node2(v___y_218_, v___y_220_, v___y_213_, v___x_231_);
v___x_233_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
v___x_234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_234_, 0, v___y_218_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
lean_inc_ref(v___y_215_);
v___x_236_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_215_, v___x_235_);
v___x_237_ = l_Lean_Syntax_node1(v___y_218_, v___y_220_, v___x_230_);
v___x_238_ = l_Lean_Syntax_node2(v___y_218_, v___x_236_, v___y_210_, v___x_237_);
v___x_239_ = lean_unsigned_to_nat(10u);
v___x_240_ = lean_mk_empty_array_with_capacity(v___x_239_);
v___x_241_ = lean_array_push(v___x_240_, v___y_214_);
v___x_242_ = lean_array_push(v___x_241_, v___y_209_);
v___x_243_ = lean_array_push(v___x_242_, v___y_216_);
v___x_244_ = lean_array_push(v___x_243_, v___y_208_);
v___x_245_ = lean_array_push(v___x_244_, v___y_207_);
v___x_246_ = lean_array_push(v___x_245_, v___y_219_);
v___x_247_ = lean_array_push(v___x_246_, v___x_224_);
v___x_248_ = lean_array_push(v___x_247_, v___x_232_);
v___x_249_ = lean_array_push(v___x_248_, v___x_234_);
v___x_250_ = lean_array_push(v___x_249_, v___x_238_);
lean_inc(v___y_221_);
v___x_251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_251_, 0, v___y_218_);
lean_ctor_set(v___x_251_, 1, v___y_221_);
lean_ctor_set(v___x_251_, 2, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___y_206_);
return v___x_252_;
}
v___jp_253_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_inc_ref(v___y_262_);
v___x_274_ = l_Array_append___redArg(v___y_262_, v___y_273_);
lean_dec_ref(v___y_273_);
lean_inc_n(v___y_267_, 4);
lean_inc_n(v___y_263_, 11);
v___x_275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_275_, 0, v___y_263_);
lean_ctor_set(v___x_275_, 1, v___y_267_);
lean_ctor_set(v___x_275_, 2, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_277_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
v___x_278_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc_n(v___y_255_, 2);
lean_inc_n(v___y_254_, 2);
v___x_279_ = l_Lean_addMacroScope(v___y_254_, v___x_278_, v___y_255_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_281_, 0, v___y_263_);
lean_ctor_set(v___x_281_, 1, v___x_277_);
lean_ctor_set(v___x_281_, 2, v___x_279_);
lean_ctor_set(v___x_281_, 3, v___x_280_);
lean_inc(v___y_260_);
v___x_282_ = l_Lean_Syntax_node2(v___y_263_, v___y_260_, v___y_256_, v___y_257_);
v___x_283_ = l_Lean_Syntax_node1(v___y_263_, v___y_267_, v___x_282_);
lean_inc_ref(v___x_281_);
v___x_284_ = l_Lean_Syntax_node2(v___y_263_, v___x_276_, v___x_281_, v___x_283_);
v___x_285_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
v___x_286_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
v___x_287_ = l_Lean_addMacroScope(v___y_254_, v___x_286_, v___y_255_);
v___x_288_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_288_, 0, v___y_263_);
lean_ctor_set(v___x_288_, 1, v___x_285_);
lean_ctor_set(v___x_288_, 2, v___x_287_);
lean_ctor_set(v___x_288_, 3, v___x_280_);
lean_inc(v___y_268_);
lean_inc_ref(v___x_288_);
v___x_289_ = l_Lean_Syntax_node2(v___y_263_, v___x_276_, v___x_288_, v___y_268_);
v___x_290_ = l_Lean_Syntax_node3(v___y_263_, v___y_267_, v___x_284_, v___y_261_, v___x_289_);
v___x_291_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
v___x_292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_292_, 0, v___y_263_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
lean_inc_ref(v___y_264_);
v___x_294_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_264_, v___x_293_);
v___x_295_ = l_Lean_Syntax_node2(v___y_263_, v___y_267_, v___x_281_, v___x_288_);
v___x_296_ = l_Lean_Syntax_node2(v___y_263_, v___x_294_, v___y_269_, v___x_295_);
v___x_297_ = lean_unsigned_to_nat(10u);
v___x_298_ = lean_mk_empty_array_with_capacity(v___x_297_);
v___x_299_ = lean_array_push(v___x_298_, v___y_266_);
v___x_300_ = lean_array_push(v___x_299_, v___y_259_);
v___x_301_ = lean_array_push(v___x_300_, v___y_272_);
v___x_302_ = lean_array_push(v___x_301_, v___y_258_);
v___x_303_ = lean_array_push(v___x_302_, v___y_268_);
v___x_304_ = lean_array_push(v___x_303_, v___y_271_);
v___x_305_ = lean_array_push(v___x_304_, v___x_275_);
v___x_306_ = lean_array_push(v___x_305_, v___x_290_);
v___x_307_ = lean_array_push(v___x_306_, v___x_292_);
v___x_308_ = lean_array_push(v___x_307_, v___x_296_);
lean_inc(v___y_265_);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___y_263_);
lean_ctor_set(v___x_309_, 1, v___y_265_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___y_270_);
return v___x_310_;
}
v___jp_311_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_inc_ref(v___y_317_);
v___x_332_ = l_Array_append___redArg(v___y_317_, v___y_331_);
lean_dec_ref(v___y_331_);
lean_inc_n(v___y_327_, 4);
lean_inc_n(v___y_324_, 11);
v___x_333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_333_, 0, v___y_324_);
lean_ctor_set(v___x_333_, 1, v___y_327_);
lean_ctor_set(v___x_333_, 2, v___x_332_);
v___x_334_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_335_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
v___x_336_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc_n(v___y_312_, 2);
lean_inc_n(v___y_323_, 2);
v___x_337_ = l_Lean_addMacroScope(v___y_323_, v___x_336_, v___y_312_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_339_, 0, v___y_324_);
lean_ctor_set(v___x_339_, 1, v___x_335_);
lean_ctor_set(v___x_339_, 2, v___x_337_);
lean_ctor_set(v___x_339_, 3, v___x_338_);
lean_inc(v___y_328_);
v___x_340_ = l_Lean_Syntax_node2(v___y_324_, v___y_328_, v___y_315_, v___y_330_);
v___x_341_ = l_Lean_Syntax_node1(v___y_324_, v___y_327_, v___x_340_);
lean_inc(v___x_341_);
lean_inc_ref(v___x_339_);
v___x_342_ = l_Lean_Syntax_node2(v___y_324_, v___x_334_, v___x_339_, v___x_341_);
v___x_343_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
v___x_344_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
v___x_345_ = l_Lean_addMacroScope(v___y_323_, v___x_344_, v___y_312_);
v___x_346_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_346_, 0, v___y_324_);
lean_ctor_set(v___x_346_, 1, v___x_343_);
lean_ctor_set(v___x_346_, 2, v___x_345_);
lean_ctor_set(v___x_346_, 3, v___x_338_);
lean_inc_ref(v___x_346_);
v___x_347_ = l_Lean_Syntax_node2(v___y_324_, v___x_334_, v___x_346_, v___x_341_);
v___x_348_ = l_Lean_Syntax_node3(v___y_324_, v___y_327_, v___x_342_, v___y_319_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
v___x_350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_350_, 0, v___y_324_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
lean_inc_ref(v___y_325_);
v___x_352_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_325_, v___x_351_);
v___x_353_ = l_Lean_Syntax_node2(v___y_324_, v___y_327_, v___x_339_, v___x_346_);
v___x_354_ = l_Lean_Syntax_node2(v___y_324_, v___x_352_, v___y_313_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(10u);
v___x_356_ = lean_mk_empty_array_with_capacity(v___x_355_);
v___x_357_ = lean_array_push(v___x_356_, v___y_320_);
v___x_358_ = lean_array_push(v___x_357_, v___y_326_);
v___x_359_ = lean_array_push(v___x_358_, v___y_316_);
v___x_360_ = lean_array_push(v___x_359_, v___y_322_);
v___x_361_ = lean_array_push(v___x_360_, v___y_318_);
v___x_362_ = lean_array_push(v___x_361_, v___y_329_);
v___x_363_ = lean_array_push(v___x_362_, v___x_333_);
v___x_364_ = lean_array_push(v___x_363_, v___x_348_);
v___x_365_ = lean_array_push(v___x_364_, v___x_350_);
v___x_366_ = lean_array_push(v___x_365_, v___x_354_);
lean_inc(v___y_321_);
v___x_367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_367_, 0, v___y_324_);
lean_ctor_set(v___x_367_, 1, v___y_321_);
lean_ctor_set(v___x_367_, 2, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___y_314_);
return v___x_368_;
}
v___jp_369_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_inc_ref(v___y_371_);
v___x_390_ = l_Array_append___redArg(v___y_371_, v___y_389_);
lean_dec_ref(v___y_389_);
lean_inc_n(v___y_382_, 4);
lean_inc_n(v___y_381_, 11);
v___x_391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_391_, 0, v___y_381_);
lean_ctor_set(v___x_391_, 1, v___y_382_);
lean_ctor_set(v___x_391_, 2, v___x_390_);
v___x_392_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
v___x_393_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
v___x_394_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc_n(v___y_370_, 2);
lean_inc_n(v___y_375_, 2);
v___x_395_ = l_Lean_addMacroScope(v___y_375_, v___x_394_, v___y_370_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_397_, 0, v___y_381_);
lean_ctor_set(v___x_397_, 1, v___x_393_);
lean_ctor_set(v___x_397_, 2, v___x_395_);
lean_ctor_set(v___x_397_, 3, v___x_396_);
lean_inc(v___y_386_);
lean_inc_ref(v___x_397_);
v___x_398_ = l_Lean_Syntax_node2(v___y_381_, v___x_392_, v___x_397_, v___y_386_);
v___x_399_ = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
v___x_400_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
v___x_401_ = l_Lean_addMacroScope(v___y_375_, v___x_400_, v___y_370_);
v___x_402_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_402_, 0, v___y_381_);
lean_ctor_set(v___x_402_, 1, v___x_399_);
lean_ctor_set(v___x_402_, 2, v___x_401_);
lean_ctor_set(v___x_402_, 3, v___x_396_);
lean_inc(v___y_383_);
v___x_403_ = l_Lean_Syntax_node2(v___y_381_, v___y_383_, v___y_387_, v___y_385_);
v___x_404_ = l_Lean_Syntax_node1(v___y_381_, v___y_382_, v___x_403_);
lean_inc_ref(v___x_402_);
v___x_405_ = l_Lean_Syntax_node2(v___y_381_, v___x_392_, v___x_402_, v___x_404_);
v___x_406_ = l_Lean_Syntax_node3(v___y_381_, v___y_382_, v___x_398_, v___y_377_, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
v___x_408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_408_, 0, v___y_381_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
lean_inc_ref(v___y_379_);
v___x_410_ = l_Lean_Name_mkStr4(v___x_155_, v___x_156_, v___y_379_, v___x_409_);
v___x_411_ = l_Lean_Syntax_node2(v___y_381_, v___y_382_, v___x_397_, v___x_402_);
v___x_412_ = l_Lean_Syntax_node2(v___y_381_, v___x_410_, v___y_388_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(10u);
v___x_414_ = lean_mk_empty_array_with_capacity(v___x_413_);
v___x_415_ = lean_array_push(v___x_414_, v___y_378_);
v___x_416_ = lean_array_push(v___x_415_, v___y_376_);
v___x_417_ = lean_array_push(v___x_416_, v___y_373_);
v___x_418_ = lean_array_push(v___x_417_, v___y_372_);
v___x_419_ = lean_array_push(v___x_418_, v___y_386_);
v___x_420_ = lean_array_push(v___x_419_, v___y_384_);
v___x_421_ = lean_array_push(v___x_420_, v___x_391_);
v___x_422_ = lean_array_push(v___x_421_, v___x_406_);
v___x_423_ = lean_array_push(v___x_422_, v___x_408_);
v___x_424_ = lean_array_push(v___x_423_, v___x_412_);
lean_inc(v___y_374_);
v___x_425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_425_, 0, v___y_381_);
lean_ctor_set(v___x_425_, 1, v___y_374_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___y_380_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___boxed(lean_object* v_stx_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Elab_Command_expandMixfix___lam__0(v_stx_1437_, v___y_1438_, v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix(lean_object* v_stx_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___f_1445_; lean_object* v___x_1446_; 
v___f_1445_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___closed__0));
v___x_1446_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(v_stx_1442_, v___f_1445_, v_a_1443_, v_a_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___boxed(lean_object* v_stx_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Elab_Command_expandMixfix(v_stx_1447_, v_a_1448_, v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1(){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1459_ = l_Lean_Elab_macroAttribute;
v___x_1460_ = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17));
v___x_1461_ = ((lean_object*)(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2));
v___x_1462_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMixfix___boxed), 3, 0);
v___x_1463_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1459_, v___x_1460_, v___x_1461_, v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___boxed(lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3(){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2));
v___x_1493_ = ((lean_object*)(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6));
v___x_1494_ = l_Lean_addBuiltinDeclarationRanges(v___x_1492_, v___x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
return v_res_1496_;
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
res = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
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
