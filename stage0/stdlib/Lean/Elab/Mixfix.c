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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_mkAttrKindGlobal;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "identPrec"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 25, 252, 182, 120, 175, 78, 126)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
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
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_mkAttrKindGlobal;
x_8 = l_Lean_Syntax_setArg(x_1, x_5, x_7);
x_9 = lean_apply_3(x_2, x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_12 = x_9;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Syntax_setArg(x_10, x_5, x_6);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_11);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_6);
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
x_22 = x_9;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_276; uint8_t x_277; 
x_4 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0));
x_5 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1));
x_276 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17));
lean_inc(x_1);
x_277 = l_Lean_Syntax_isOfKind(x_1, x_276);
if (x_277 == 0)
{
lean_object* x_278; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_278 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_710; uint8_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_754; uint8_t x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; uint8_t x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint8_t x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1275; uint8_t x_1276; 
x_279 = lean_unsigned_to_nat(0u);
x_1275 = l_Lean_Syntax_getArg(x_1, x_279);
x_1276 = l_Lean_Syntax_isNone(x_1275);
if (x_1276 == 0)
{
lean_object* x_1277; uint8_t x_1278; 
x_1277 = lean_unsigned_to_nat(1u);
lean_inc(x_1275);
x_1278 = l_Lean_Syntax_matchesNull(x_1275, x_1277);
if (x_1278 == 0)
{
lean_object* x_1279; 
lean_dec(x_1275);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1279 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_1279;
}
else
{
lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; 
x_1280 = l_Lean_Syntax_getArg(x_1275, x_279);
lean_dec(x_1275);
x_1281 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54));
lean_inc(x_1280);
x_1282 = l_Lean_Syntax_isOfKind(x_1280, x_1281);
if (x_1282 == 0)
{
lean_object* x_1283; 
lean_dec(x_1280);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1283 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_1283;
}
else
{
lean_object* x_1284; 
x_1284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1284, 0, x_1280);
x_1258 = x_1284;
x_1259 = x_2;
x_1260 = x_3;
goto block_1274;
}
}
}
else
{
lean_object* x_1285; 
lean_dec(x_1275);
x_1285 = lean_box(0);
x_1258 = x_1285;
x_1259 = x_2;
x_1260 = x_3;
goto block_1274;
}
block_312:
{
lean_object* x_297; lean_object* x_298; 
lean_inc_ref(x_285);
x_297 = l_Array_append___redArg(x_285, x_296);
lean_dec_ref(x_296);
lean_inc(x_288);
lean_inc(x_290);
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_290);
lean_ctor_set(x_298, 1, x_288);
lean_ctor_set(x_298, 2, x_297);
if (lean_obj_tag(x_292) == 1)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_299 = lean_ctor_get(x_292, 0);
lean_inc(x_299);
lean_dec_ref(x_292);
x_300 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
x_301 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_290);
x_302 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_302, 0, x_290);
lean_ctor_set(x_302, 1, x_301);
x_303 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_290);
x_304 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_304, 0, x_290);
lean_ctor_set(x_304, 1, x_303);
x_305 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_290);
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_290);
lean_ctor_set(x_306, 1, x_305);
x_307 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_290);
x_308 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_308, 0, x_290);
lean_ctor_set(x_308, 1, x_307);
lean_inc(x_290);
x_309 = l_Lean_Syntax_node5(x_290, x_300, x_302, x_304, x_306, x_299, x_308);
x_310 = l_Array_mkArray1___redArg(x_309);
x_6 = x_280;
x_7 = x_281;
x_8 = x_282;
x_9 = x_283;
x_10 = x_284;
x_11 = x_285;
x_12 = x_286;
x_13 = x_287;
x_14 = x_288;
x_15 = x_289;
x_16 = x_290;
x_17 = x_291;
x_18 = x_298;
x_19 = x_293;
x_20 = x_294;
x_21 = x_295;
x_22 = x_310;
goto block_53;
}
else
{
lean_object* x_311; 
lean_dec(x_292);
x_311 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_6 = x_280;
x_7 = x_281;
x_8 = x_282;
x_9 = x_283;
x_10 = x_284;
x_11 = x_285;
x_12 = x_286;
x_13 = x_287;
x_14 = x_288;
x_15 = x_289;
x_16 = x_290;
x_17 = x_291;
x_18 = x_298;
x_19 = x_293;
x_20 = x_294;
x_21 = x_295;
x_22 = x_311;
goto block_53;
}
}
block_353:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_inc_ref(x_318);
x_331 = l_Array_append___redArg(x_318, x_330);
lean_dec_ref(x_330);
lean_inc(x_320);
lean_inc(x_323);
x_332 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_332, 0, x_323);
lean_ctor_set(x_332, 1, x_320);
lean_ctor_set(x_332, 2, x_331);
lean_inc_ref(x_318);
lean_inc(x_320);
lean_inc(x_323);
x_333 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_333, 0, x_323);
lean_ctor_set(x_333, 1, x_320);
lean_ctor_set(x_333, 2, x_318);
lean_inc(x_323);
x_334 = l_Lean_Syntax_node1(x_323, x_321, x_333);
lean_inc(x_323);
x_335 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_335, 0, x_323);
lean_ctor_set(x_335, 1, x_315);
x_336 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(x_323);
x_337 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_337, 0, x_323);
lean_ctor_set(x_337, 1, x_336);
lean_inc(x_323);
x_338 = l_Lean_Syntax_node2(x_323, x_325, x_337, x_326);
lean_inc(x_320);
lean_inc(x_323);
x_339 = l_Lean_Syntax_node1(x_323, x_320, x_338);
if (lean_obj_tag(x_328) == 1)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_340 = lean_ctor_get(x_328, 0);
lean_inc(x_340);
lean_dec_ref(x_328);
x_341 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
x_342 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_323);
x_343 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_343, 0, x_323);
lean_ctor_set(x_343, 1, x_342);
x_344 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_323);
x_345 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_345, 0, x_323);
lean_ctor_set(x_345, 1, x_344);
x_346 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_323);
x_347 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_347, 0, x_323);
lean_ctor_set(x_347, 1, x_346);
x_348 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_323);
x_349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_349, 0, x_323);
lean_ctor_set(x_349, 1, x_348);
lean_inc(x_323);
x_350 = l_Lean_Syntax_node5(x_323, x_341, x_343, x_345, x_347, x_340, x_349);
x_351 = l_Array_mkArray1___redArg(x_350);
x_280 = x_313;
x_281 = x_314;
x_282 = x_316;
x_283 = x_317;
x_284 = x_332;
x_285 = x_318;
x_286 = x_319;
x_287 = x_335;
x_288 = x_320;
x_289 = x_322;
x_290 = x_323;
x_291 = x_339;
x_292 = x_324;
x_293 = x_334;
x_294 = x_327;
x_295 = x_329;
x_296 = x_351;
goto block_312;
}
else
{
lean_object* x_352; 
lean_dec(x_328);
x_352 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_280 = x_313;
x_281 = x_314;
x_282 = x_316;
x_283 = x_317;
x_284 = x_332;
x_285 = x_318;
x_286 = x_319;
x_287 = x_335;
x_288 = x_320;
x_289 = x_322;
x_290 = x_323;
x_291 = x_339;
x_292 = x_324;
x_293 = x_334;
x_294 = x_327;
x_295 = x_329;
x_296 = x_352;
goto block_312;
}
}
block_386:
{
lean_object* x_372; lean_object* x_373; 
lean_inc_ref(x_359);
x_372 = l_Array_append___redArg(x_359, x_371);
lean_dec_ref(x_371);
lean_inc(x_361);
lean_inc(x_364);
x_373 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_373, 0, x_364);
lean_ctor_set(x_373, 1, x_361);
lean_ctor_set(x_373, 2, x_372);
if (lean_obj_tag(x_358) == 1)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_374 = lean_ctor_get(x_358, 0);
lean_inc(x_374);
lean_dec_ref(x_358);
x_375 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(x_368);
x_376 = l_Lean_Name_mkStr4(x_4, x_5, x_368, x_375);
x_377 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(x_364);
x_378 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_378, 0, x_364);
lean_ctor_set(x_378, 1, x_377);
lean_inc_ref(x_359);
x_379 = l_Array_append___redArg(x_359, x_374);
lean_dec(x_374);
lean_inc(x_361);
lean_inc(x_364);
x_380 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_380, 0, x_364);
lean_ctor_set(x_380, 1, x_361);
lean_ctor_set(x_380, 2, x_379);
x_381 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_364);
x_382 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_382, 0, x_364);
lean_ctor_set(x_382, 1, x_381);
lean_inc(x_364);
x_383 = l_Lean_Syntax_node3(x_364, x_376, x_378, x_380, x_382);
x_384 = l_Array_mkArray1___redArg(x_383);
x_313 = x_354;
x_314 = x_373;
x_315 = x_355;
x_316 = x_356;
x_317 = x_357;
x_318 = x_359;
x_319 = x_360;
x_320 = x_361;
x_321 = x_362;
x_322 = x_363;
x_323 = x_364;
x_324 = x_365;
x_325 = x_366;
x_326 = x_367;
x_327 = x_368;
x_328 = x_370;
x_329 = x_369;
x_330 = x_384;
goto block_353;
}
else
{
lean_object* x_385; 
lean_dec(x_358);
x_385 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_313 = x_354;
x_314 = x_373;
x_315 = x_355;
x_316 = x_356;
x_317 = x_357;
x_318 = x_359;
x_319 = x_360;
x_320 = x_361;
x_321 = x_362;
x_322 = x_363;
x_323 = x_364;
x_324 = x_365;
x_325 = x_366;
x_326 = x_367;
x_327 = x_368;
x_328 = x_370;
x_329 = x_369;
x_330 = x_385;
goto block_353;
}
}
block_413:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_396, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_396, 5);
lean_inc(x_400);
lean_dec_ref(x_396);
x_401 = lean_unsigned_to_nat(7u);
x_402 = l_Lean_Syntax_getArg(x_1, x_401);
x_403 = lean_unsigned_to_nat(9u);
x_404 = l_Lean_Syntax_getArg(x_1, x_403);
lean_dec(x_1);
x_405 = l_Lean_SourceInfo_fromRef(x_400, x_390);
lean_dec(x_400);
x_406 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
x_407 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_408 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
x_409 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(x_387) == 1)
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_387, 0);
lean_inc(x_410);
lean_dec_ref(x_387);
x_411 = l_Array_mkArray1___redArg(x_410);
x_354 = x_402;
x_355 = x_406;
x_356 = x_407;
x_357 = x_404;
x_358 = x_391;
x_359 = x_409;
x_360 = x_398;
x_361 = x_408;
x_362 = x_392;
x_363 = x_397;
x_364 = x_405;
x_365 = x_395;
x_366 = x_389;
x_367 = x_388;
x_368 = x_393;
x_369 = x_399;
x_370 = x_394;
x_371 = x_411;
goto block_386;
}
else
{
lean_object* x_412; 
lean_dec(x_387);
x_412 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_354 = x_402;
x_355 = x_406;
x_356 = x_407;
x_357 = x_404;
x_358 = x_391;
x_359 = x_409;
x_360 = x_398;
x_361 = x_408;
x_362 = x_392;
x_363 = x_397;
x_364 = x_405;
x_365 = x_395;
x_366 = x_389;
x_367 = x_388;
x_368 = x_393;
x_369 = x_399;
x_370 = x_394;
x_371 = x_412;
goto block_386;
}
}
block_438:
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_426 = lean_unsigned_to_nat(6u);
x_427 = l_Lean_Syntax_getArg(x_1, x_426);
x_428 = l_Lean_Syntax_isNone(x_427);
if (x_428 == 0)
{
uint8_t x_429; 
lean_inc(x_427);
x_429 = l_Lean_Syntax_matchesNull(x_427, x_422);
if (x_429 == 0)
{
lean_object* x_430; 
lean_dec(x_427);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_1);
x_430 = l_Lean_Macro_throwUnsupported___redArg(x_425);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_431 = l_Lean_Syntax_getArg(x_427, x_279);
lean_dec(x_427);
x_432 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(x_431);
x_433 = l_Lean_Syntax_isOfKind(x_431, x_432);
if (x_433 == 0)
{
lean_object* x_434; 
lean_dec(x_431);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_1);
x_434 = l_Lean_Macro_throwUnsupported___redArg(x_425);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; 
x_435 = l_Lean_Syntax_getArg(x_431, x_418);
lean_dec(x_431);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
x_387 = x_414;
x_388 = x_417;
x_389 = x_416;
x_390 = x_415;
x_391 = x_419;
x_392 = x_420;
x_393 = x_421;
x_394 = x_423;
x_395 = x_436;
x_396 = x_424;
x_397 = x_425;
goto block_413;
}
}
}
else
{
lean_object* x_437; 
lean_dec(x_427);
x_437 = lean_box(0);
x_387 = x_414;
x_388 = x_417;
x_389 = x_416;
x_390 = x_415;
x_391 = x_419;
x_392 = x_420;
x_393 = x_421;
x_394 = x_423;
x_395 = x_437;
x_396 = x_424;
x_397 = x_425;
goto block_413;
}
}
block_471:
{
lean_object* x_456; lean_object* x_457; 
lean_inc_ref(x_439);
x_456 = l_Array_append___redArg(x_439, x_455);
lean_dec_ref(x_455);
lean_inc(x_449);
lean_inc(x_452);
x_457 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_457, 0, x_452);
lean_ctor_set(x_457, 1, x_449);
lean_ctor_set(x_457, 2, x_456);
if (lean_obj_tag(x_447) == 1)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_458 = lean_ctor_get(x_447, 0);
lean_inc(x_458);
lean_dec_ref(x_447);
x_459 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
x_460 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_452);
x_461 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_461, 0, x_452);
lean_ctor_set(x_461, 1, x_460);
x_462 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_452);
x_463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_463, 0, x_452);
lean_ctor_set(x_463, 1, x_462);
x_464 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_452);
x_465 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_465, 0, x_452);
lean_ctor_set(x_465, 1, x_464);
x_466 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_452);
x_467 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_467, 0, x_452);
lean_ctor_set(x_467, 1, x_466);
lean_inc(x_452);
x_468 = l_Lean_Syntax_node5(x_452, x_459, x_461, x_463, x_465, x_458, x_467);
x_469 = l_Array_mkArray1___redArg(x_468);
x_54 = x_439;
x_55 = x_440;
x_56 = x_441;
x_57 = x_442;
x_58 = x_443;
x_59 = x_444;
x_60 = x_445;
x_61 = x_446;
x_62 = x_448;
x_63 = x_449;
x_64 = x_457;
x_65 = x_450;
x_66 = x_451;
x_67 = x_452;
x_68 = x_454;
x_69 = x_453;
x_70 = x_469;
goto block_101;
}
else
{
lean_object* x_470; 
lean_dec(x_447);
x_470 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_54 = x_439;
x_55 = x_440;
x_56 = x_441;
x_57 = x_442;
x_58 = x_443;
x_59 = x_444;
x_60 = x_445;
x_61 = x_446;
x_62 = x_448;
x_63 = x_449;
x_64 = x_457;
x_65 = x_450;
x_66 = x_451;
x_67 = x_452;
x_68 = x_454;
x_69 = x_453;
x_70 = x_470;
goto block_101;
}
}
block_512:
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_inc_ref(x_472);
x_490 = l_Array_append___redArg(x_472, x_489);
lean_dec_ref(x_489);
lean_inc(x_482);
lean_inc(x_484);
x_491 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_491, 0, x_484);
lean_ctor_set(x_491, 1, x_482);
lean_ctor_set(x_491, 2, x_490);
lean_inc_ref(x_472);
lean_inc(x_482);
lean_inc(x_484);
x_492 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_492, 0, x_484);
lean_ctor_set(x_492, 1, x_482);
lean_ctor_set(x_492, 2, x_472);
lean_inc(x_484);
x_493 = l_Lean_Syntax_node1(x_484, x_477, x_492);
lean_inc(x_484);
x_494 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_494, 0, x_484);
lean_ctor_set(x_494, 1, x_485);
x_495 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(x_484);
x_496 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_496, 0, x_484);
lean_ctor_set(x_496, 1, x_495);
lean_inc(x_484);
x_497 = l_Lean_Syntax_node2(x_484, x_473, x_496, x_478);
lean_inc(x_482);
lean_inc(x_484);
x_498 = l_Lean_Syntax_node1(x_484, x_482, x_497);
if (lean_obj_tag(x_486) == 1)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_499 = lean_ctor_get(x_486, 0);
lean_inc(x_499);
lean_dec_ref(x_486);
x_500 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
x_501 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_484);
x_502 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_502, 0, x_484);
lean_ctor_set(x_502, 1, x_501);
x_503 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_484);
x_504 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_504, 0, x_484);
lean_ctor_set(x_504, 1, x_503);
x_505 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_484);
x_506 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_506, 0, x_484);
lean_ctor_set(x_506, 1, x_505);
x_507 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_484);
x_508 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_508, 0, x_484);
lean_ctor_set(x_508, 1, x_507);
lean_inc(x_484);
x_509 = l_Lean_Syntax_node5(x_484, x_500, x_502, x_504, x_506, x_499, x_508);
x_510 = l_Array_mkArray1___redArg(x_509);
x_439 = x_472;
x_440 = x_474;
x_441 = x_475;
x_442 = x_498;
x_443 = x_476;
x_444 = x_494;
x_445 = x_491;
x_446 = x_479;
x_447 = x_480;
x_448 = x_481;
x_449 = x_482;
x_450 = x_483;
x_451 = x_493;
x_452 = x_484;
x_453 = x_488;
x_454 = x_487;
x_455 = x_510;
goto block_471;
}
else
{
lean_object* x_511; 
lean_dec(x_486);
x_511 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_439 = x_472;
x_440 = x_474;
x_441 = x_475;
x_442 = x_498;
x_443 = x_476;
x_444 = x_494;
x_445 = x_491;
x_446 = x_479;
x_447 = x_480;
x_448 = x_481;
x_449 = x_482;
x_450 = x_483;
x_451 = x_493;
x_452 = x_484;
x_453 = x_488;
x_454 = x_487;
x_455 = x_511;
goto block_471;
}
}
block_545:
{
lean_object* x_531; lean_object* x_532; 
lean_inc_ref(x_513);
x_531 = l_Array_append___redArg(x_513, x_530);
lean_dec_ref(x_530);
lean_inc(x_524);
lean_inc(x_525);
x_532 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_532, 0, x_525);
lean_ctor_set(x_532, 1, x_524);
lean_ctor_set(x_532, 2, x_531);
if (lean_obj_tag(x_518) == 1)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_533 = lean_ctor_get(x_518, 0);
lean_inc(x_533);
lean_dec_ref(x_518);
x_534 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(x_527);
x_535 = l_Lean_Name_mkStr4(x_4, x_5, x_527, x_534);
x_536 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(x_525);
x_537 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_537, 0, x_525);
lean_ctor_set(x_537, 1, x_536);
lean_inc_ref(x_513);
x_538 = l_Array_append___redArg(x_513, x_533);
lean_dec(x_533);
lean_inc(x_524);
lean_inc(x_525);
x_539 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_539, 0, x_525);
lean_ctor_set(x_539, 1, x_524);
lean_ctor_set(x_539, 2, x_538);
x_540 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_525);
x_541 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_541, 0, x_525);
lean_ctor_set(x_541, 1, x_540);
lean_inc(x_525);
x_542 = l_Lean_Syntax_node3(x_525, x_535, x_537, x_539, x_541);
x_543 = l_Array_mkArray1___redArg(x_542);
x_472 = x_513;
x_473 = x_514;
x_474 = x_515;
x_475 = x_516;
x_476 = x_517;
x_477 = x_519;
x_478 = x_520;
x_479 = x_521;
x_480 = x_522;
x_481 = x_523;
x_482 = x_524;
x_483 = x_532;
x_484 = x_525;
x_485 = x_526;
x_486 = x_529;
x_487 = x_528;
x_488 = x_527;
x_489 = x_543;
goto block_512;
}
else
{
lean_object* x_544; 
lean_dec(x_518);
x_544 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_472 = x_513;
x_473 = x_514;
x_474 = x_515;
x_475 = x_516;
x_476 = x_517;
x_477 = x_519;
x_478 = x_520;
x_479 = x_521;
x_480 = x_522;
x_481 = x_523;
x_482 = x_524;
x_483 = x_532;
x_484 = x_525;
x_485 = x_526;
x_486 = x_529;
x_487 = x_528;
x_488 = x_527;
x_489 = x_544;
goto block_512;
}
}
block_572:
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
x_558 = lean_ctor_get(x_555, 2);
lean_inc(x_558);
x_559 = lean_ctor_get(x_555, 5);
lean_inc(x_559);
lean_dec_ref(x_555);
x_560 = lean_unsigned_to_nat(7u);
x_561 = l_Lean_Syntax_getArg(x_1, x_560);
x_562 = lean_unsigned_to_nat(9u);
x_563 = l_Lean_Syntax_getArg(x_1, x_562);
lean_dec(x_1);
x_564 = l_Lean_SourceInfo_fromRef(x_559, x_550);
lean_dec(x_559);
x_565 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
x_566 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_567 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
x_568 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(x_547) == 1)
{
lean_object* x_569; lean_object* x_570; 
x_569 = lean_ctor_get(x_547, 0);
lean_inc(x_569);
lean_dec_ref(x_547);
x_570 = l_Array_mkArray1___redArg(x_569);
x_513 = x_568;
x_514 = x_546;
x_515 = x_558;
x_516 = x_561;
x_517 = x_566;
x_518 = x_548;
x_519 = x_549;
x_520 = x_553;
x_521 = x_556;
x_522 = x_554;
x_523 = x_563;
x_524 = x_567;
x_525 = x_564;
x_526 = x_565;
x_527 = x_552;
x_528 = x_557;
x_529 = x_551;
x_530 = x_570;
goto block_545;
}
else
{
lean_object* x_571; 
lean_dec(x_547);
x_571 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_513 = x_568;
x_514 = x_546;
x_515 = x_558;
x_516 = x_561;
x_517 = x_566;
x_518 = x_548;
x_519 = x_549;
x_520 = x_553;
x_521 = x_556;
x_522 = x_554;
x_523 = x_563;
x_524 = x_567;
x_525 = x_564;
x_526 = x_565;
x_527 = x_552;
x_528 = x_557;
x_529 = x_551;
x_530 = x_571;
goto block_545;
}
}
block_597:
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_585 = lean_unsigned_to_nat(6u);
x_586 = l_Lean_Syntax_getArg(x_1, x_585);
x_587 = l_Lean_Syntax_isNone(x_586);
if (x_587 == 0)
{
uint8_t x_588; 
lean_inc(x_586);
x_588 = l_Lean_Syntax_matchesNull(x_586, x_581);
if (x_588 == 0)
{
lean_object* x_589; 
lean_dec(x_586);
lean_dec_ref(x_583);
lean_dec(x_582);
lean_dec_ref(x_580);
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_1);
x_589 = l_Lean_Macro_throwUnsupported___redArg(x_584);
return x_589;
}
else
{
lean_object* x_590; lean_object* x_591; uint8_t x_592; 
x_590 = l_Lean_Syntax_getArg(x_586, x_279);
lean_dec(x_586);
x_591 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(x_590);
x_592 = l_Lean_Syntax_isOfKind(x_590, x_591);
if (x_592 == 0)
{
lean_object* x_593; 
lean_dec(x_590);
lean_dec_ref(x_583);
lean_dec(x_582);
lean_dec_ref(x_580);
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_1);
x_593 = l_Lean_Macro_throwUnsupported___redArg(x_584);
return x_593;
}
else
{
lean_object* x_594; lean_object* x_595; 
x_594 = l_Lean_Syntax_getArg(x_590, x_575);
lean_dec(x_590);
x_595 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_595, 0, x_594);
x_546 = x_573;
x_547 = x_574;
x_548 = x_576;
x_549 = x_578;
x_550 = x_577;
x_551 = x_582;
x_552 = x_580;
x_553 = x_579;
x_554 = x_595;
x_555 = x_583;
x_556 = x_584;
goto block_572;
}
}
}
else
{
lean_object* x_596; 
lean_dec(x_586);
x_596 = lean_box(0);
x_546 = x_573;
x_547 = x_574;
x_548 = x_576;
x_549 = x_578;
x_550 = x_577;
x_551 = x_582;
x_552 = x_580;
x_553 = x_579;
x_554 = x_596;
x_555 = x_583;
x_556 = x_584;
goto block_572;
}
}
block_633:
{
lean_object* x_618; lean_object* x_619; 
lean_inc_ref(x_615);
x_618 = l_Array_append___redArg(x_615, x_617);
lean_dec_ref(x_617);
lean_inc(x_613);
lean_inc(x_599);
x_619 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_619, 0, x_599);
lean_ctor_set(x_619, 1, x_613);
lean_ctor_set(x_619, 2, x_618);
if (lean_obj_tag(x_604) == 1)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_620 = lean_ctor_get(x_604, 0);
lean_inc(x_620);
lean_dec_ref(x_604);
x_621 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
x_622 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_599);
x_623 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_623, 0, x_599);
lean_ctor_set(x_623, 1, x_622);
x_624 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_599);
x_625 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_625, 0, x_599);
lean_ctor_set(x_625, 1, x_624);
x_626 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_599);
x_627 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_627, 0, x_599);
lean_ctor_set(x_627, 1, x_626);
x_628 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_599);
x_629 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_629, 0, x_599);
lean_ctor_set(x_629, 1, x_628);
lean_inc(x_599);
x_630 = l_Lean_Syntax_node5(x_599, x_621, x_623, x_625, x_627, x_620, x_629);
x_631 = l_Array_mkArray1___redArg(x_630);
x_102 = x_598;
x_103 = x_599;
x_104 = x_600;
x_105 = x_601;
x_106 = x_602;
x_107 = x_603;
x_108 = x_605;
x_109 = x_606;
x_110 = x_607;
x_111 = x_608;
x_112 = x_609;
x_113 = x_610;
x_114 = x_613;
x_115 = x_612;
x_116 = x_611;
x_117 = x_614;
x_118 = x_615;
x_119 = x_616;
x_120 = x_619;
x_121 = x_631;
goto block_159;
}
else
{
lean_object* x_632; 
lean_dec(x_604);
x_632 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_102 = x_598;
x_103 = x_599;
x_104 = x_600;
x_105 = x_601;
x_106 = x_602;
x_107 = x_603;
x_108 = x_605;
x_109 = x_606;
x_110 = x_607;
x_111 = x_608;
x_112 = x_609;
x_113 = x_610;
x_114 = x_613;
x_115 = x_612;
x_116 = x_611;
x_117 = x_614;
x_118 = x_615;
x_119 = x_616;
x_120 = x_619;
x_121 = x_632;
goto block_159;
}
}
block_675:
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_inc_ref(x_649);
x_653 = l_Array_append___redArg(x_649, x_652);
lean_dec_ref(x_652);
lean_inc(x_647);
lean_inc(x_634);
x_654 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_654, 0, x_634);
lean_ctor_set(x_654, 1, x_647);
lean_ctor_set(x_654, 2, x_653);
lean_inc_ref(x_649);
lean_inc(x_647);
lean_inc(x_634);
x_655 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_655, 0, x_634);
lean_ctor_set(x_655, 1, x_647);
lean_ctor_set(x_655, 2, x_649);
lean_inc(x_634);
x_656 = l_Lean_Syntax_node1(x_634, x_641, x_655);
lean_inc(x_634);
x_657 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_657, 0, x_634);
lean_ctor_set(x_657, 1, x_651);
x_658 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(x_634);
x_659 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_659, 0, x_634);
lean_ctor_set(x_659, 1, x_658);
lean_inc_ref(x_659);
lean_inc(x_642);
lean_inc(x_634);
x_660 = l_Lean_Syntax_node2(x_634, x_642, x_659, x_644);
lean_inc(x_647);
lean_inc(x_634);
x_661 = l_Lean_Syntax_node1(x_634, x_647, x_660);
if (lean_obj_tag(x_638) == 1)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_662 = lean_ctor_get(x_638, 0);
lean_inc(x_662);
lean_dec_ref(x_638);
x_663 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
x_664 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_634);
x_665 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_665, 0, x_634);
lean_ctor_set(x_665, 1, x_664);
x_666 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_634);
x_667 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_667, 0, x_634);
lean_ctor_set(x_667, 1, x_666);
x_668 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_634);
x_669 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_669, 0, x_634);
lean_ctor_set(x_669, 1, x_668);
x_670 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_634);
x_671 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_671, 0, x_634);
lean_ctor_set(x_671, 1, x_670);
lean_inc(x_634);
x_672 = l_Lean_Syntax_node5(x_634, x_663, x_665, x_667, x_669, x_662, x_671);
x_673 = l_Array_mkArray1___redArg(x_672);
x_598 = x_659;
x_599 = x_634;
x_600 = x_635;
x_601 = x_654;
x_602 = x_636;
x_603 = x_637;
x_604 = x_639;
x_605 = x_640;
x_606 = x_656;
x_607 = x_642;
x_608 = x_661;
x_609 = x_643;
x_610 = x_657;
x_611 = x_646;
x_612 = x_645;
x_613 = x_647;
x_614 = x_648;
x_615 = x_649;
x_616 = x_650;
x_617 = x_673;
goto block_633;
}
else
{
lean_object* x_674; 
lean_dec(x_638);
x_674 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_598 = x_659;
x_599 = x_634;
x_600 = x_635;
x_601 = x_654;
x_602 = x_636;
x_603 = x_637;
x_604 = x_639;
x_605 = x_640;
x_606 = x_656;
x_607 = x_642;
x_608 = x_661;
x_609 = x_643;
x_610 = x_657;
x_611 = x_646;
x_612 = x_645;
x_613 = x_647;
x_614 = x_648;
x_615 = x_649;
x_616 = x_650;
x_617 = x_674;
goto block_633;
}
}
block_709:
{
lean_object* x_695; lean_object* x_696; 
lean_inc_ref(x_691);
x_695 = l_Array_append___redArg(x_691, x_694);
lean_dec_ref(x_694);
lean_inc(x_689);
lean_inc(x_676);
x_696 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_696, 0, x_676);
lean_ctor_set(x_696, 1, x_689);
lean_ctor_set(x_696, 2, x_695);
if (lean_obj_tag(x_680) == 1)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_697 = lean_ctor_get(x_680, 0);
lean_inc(x_697);
lean_dec_ref(x_680);
x_698 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(x_692);
x_699 = l_Lean_Name_mkStr4(x_4, x_5, x_692, x_698);
x_700 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(x_676);
x_701 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_701, 0, x_676);
lean_ctor_set(x_701, 1, x_700);
lean_inc_ref(x_691);
x_702 = l_Array_append___redArg(x_691, x_697);
lean_dec(x_697);
lean_inc(x_689);
lean_inc(x_676);
x_703 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_703, 0, x_676);
lean_ctor_set(x_703, 1, x_689);
lean_ctor_set(x_703, 2, x_702);
x_704 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_676);
x_705 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_705, 0, x_676);
lean_ctor_set(x_705, 1, x_704);
lean_inc(x_676);
x_706 = l_Lean_Syntax_node3(x_676, x_699, x_701, x_703, x_705);
x_707 = l_Array_mkArray1___redArg(x_706);
x_634 = x_676;
x_635 = x_677;
x_636 = x_678;
x_637 = x_679;
x_638 = x_681;
x_639 = x_682;
x_640 = x_683;
x_641 = x_684;
x_642 = x_685;
x_643 = x_686;
x_644 = x_687;
x_645 = x_688;
x_646 = x_696;
x_647 = x_689;
x_648 = x_690;
x_649 = x_691;
x_650 = x_692;
x_651 = x_693;
x_652 = x_707;
goto block_675;
}
else
{
lean_object* x_708; 
lean_dec(x_680);
x_708 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_634 = x_676;
x_635 = x_677;
x_636 = x_678;
x_637 = x_679;
x_638 = x_681;
x_639 = x_682;
x_640 = x_683;
x_641 = x_684;
x_642 = x_685;
x_643 = x_686;
x_644 = x_687;
x_645 = x_688;
x_646 = x_696;
x_647 = x_689;
x_648 = x_690;
x_649 = x_691;
x_650 = x_692;
x_651 = x_693;
x_652 = x_708;
goto block_675;
}
}
block_753:
{
lean_object* x_722; 
lean_inc_ref(x_720);
lean_inc(x_712);
x_722 = l_Lean_evalPrec(x_712, x_720, x_721);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec_ref(x_722);
x_725 = lean_ctor_get(x_720, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_720, 2);
lean_inc(x_726);
x_727 = lean_ctor_get(x_720, 5);
lean_inc(x_727);
lean_dec_ref(x_720);
x_728 = lean_unsigned_to_nat(7u);
x_729 = l_Lean_Syntax_getArg(x_1, x_728);
x_730 = lean_unsigned_to_nat(9u);
x_731 = l_Lean_Syntax_getArg(x_1, x_730);
lean_dec(x_1);
x_732 = lean_nat_add(x_723, x_718);
lean_dec(x_723);
x_733 = l_Nat_reprFast(x_732);
x_734 = lean_box(2);
x_735 = l_Lean_Syntax_mkNumLit(x_733, x_734);
x_736 = l_Lean_SourceInfo_fromRef(x_727, x_711);
lean_dec(x_727);
x_737 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
x_738 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_739 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
x_740 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(x_710) == 1)
{
lean_object* x_741; lean_object* x_742; 
x_741 = lean_ctor_get(x_710, 0);
lean_inc(x_741);
lean_dec_ref(x_710);
x_742 = l_Array_mkArray1___redArg(x_741);
x_676 = x_736;
x_677 = x_738;
x_678 = x_725;
x_679 = x_724;
x_680 = x_714;
x_681 = x_713;
x_682 = x_719;
x_683 = x_729;
x_684 = x_716;
x_685 = x_715;
x_686 = x_735;
x_687 = x_712;
x_688 = x_726;
x_689 = x_739;
x_690 = x_731;
x_691 = x_740;
x_692 = x_717;
x_693 = x_737;
x_694 = x_742;
goto block_709;
}
else
{
lean_object* x_743; 
lean_dec(x_710);
x_743 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_676 = x_736;
x_677 = x_738;
x_678 = x_725;
x_679 = x_724;
x_680 = x_714;
x_681 = x_713;
x_682 = x_719;
x_683 = x_729;
x_684 = x_716;
x_685 = x_715;
x_686 = x_735;
x_687 = x_712;
x_688 = x_726;
x_689 = x_739;
x_690 = x_731;
x_691 = x_740;
x_692 = x_717;
x_693 = x_737;
x_694 = x_743;
goto block_709;
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; uint8_t x_752; 
lean_dec_ref(x_720);
lean_dec(x_719);
lean_dec_ref(x_717);
lean_dec(x_716);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_710);
lean_dec(x_1);
x_744 = lean_ctor_get(x_722, 0);
x_745 = lean_ctor_get(x_722, 1);
x_752 = !lean_is_exclusive(x_722);
if (x_752 == 0)
{
x_746 = x_722;
x_747 = x_752;
goto block_751;
}
else
{
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_722);
x_746 = lean_box(0);
x_747 = x_752;
goto block_751;
}
block_751:
{
lean_object* x_748; 
if (x_747 == 0)
{
x_748 = x_746;
goto block_749;
}
else
{
lean_object* x_750; 
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_744);
lean_ctor_set(x_750, 1, x_745);
x_748 = x_750;
goto block_749;
}
block_749:
{
return x_748;
}
}
}
}
block_778:
{
lean_object* x_766; lean_object* x_767; uint8_t x_768; 
x_766 = lean_unsigned_to_nat(6u);
x_767 = l_Lean_Syntax_getArg(x_1, x_766);
x_768 = l_Lean_Syntax_isNone(x_767);
if (x_768 == 0)
{
uint8_t x_769; 
lean_inc(x_767);
x_769 = l_Lean_Syntax_matchesNull(x_767, x_762);
if (x_769 == 0)
{
lean_object* x_770; 
lean_dec(x_767);
lean_dec_ref(x_764);
lean_dec(x_763);
lean_dec_ref(x_761);
lean_dec(x_760);
lean_dec(x_759);
lean_dec(x_758);
lean_dec(x_756);
lean_dec(x_754);
lean_dec(x_1);
x_770 = l_Lean_Macro_throwUnsupported___redArg(x_765);
return x_770;
}
else
{
lean_object* x_771; lean_object* x_772; uint8_t x_773; 
x_771 = l_Lean_Syntax_getArg(x_767, x_279);
lean_dec(x_767);
x_772 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(x_771);
x_773 = l_Lean_Syntax_isOfKind(x_771, x_772);
if (x_773 == 0)
{
lean_object* x_774; 
lean_dec(x_771);
lean_dec_ref(x_764);
lean_dec(x_763);
lean_dec_ref(x_761);
lean_dec(x_760);
lean_dec(x_759);
lean_dec(x_758);
lean_dec(x_756);
lean_dec(x_754);
lean_dec(x_1);
x_774 = l_Lean_Macro_throwUnsupported___redArg(x_765);
return x_774;
}
else
{
lean_object* x_775; lean_object* x_776; 
x_775 = l_Lean_Syntax_getArg(x_771, x_757);
lean_dec(x_771);
x_776 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_776, 0, x_775);
x_710 = x_754;
x_711 = x_755;
x_712 = x_756;
x_713 = x_763;
x_714 = x_758;
x_715 = x_760;
x_716 = x_759;
x_717 = x_761;
x_718 = x_762;
x_719 = x_776;
x_720 = x_764;
x_721 = x_765;
goto block_753;
}
}
}
else
{
lean_object* x_777; 
lean_dec(x_767);
x_777 = lean_box(0);
x_710 = x_754;
x_711 = x_755;
x_712 = x_756;
x_713 = x_763;
x_714 = x_758;
x_715 = x_760;
x_716 = x_759;
x_717 = x_761;
x_718 = x_762;
x_719 = x_777;
x_720 = x_764;
x_721 = x_765;
goto block_753;
}
}
block_814:
{
lean_object* x_799; lean_object* x_800; 
lean_inc_ref(x_794);
x_799 = l_Array_append___redArg(x_794, x_798);
lean_dec_ref(x_798);
lean_inc(x_787);
lean_inc(x_779);
x_800 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_800, 0, x_779);
lean_ctor_set(x_800, 1, x_787);
lean_ctor_set(x_800, 2, x_799);
if (lean_obj_tag(x_796) == 1)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_801 = lean_ctor_get(x_796, 0);
lean_inc(x_801);
lean_dec_ref(x_796);
x_802 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
x_803 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_779);
x_804 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_804, 0, x_779);
lean_ctor_set(x_804, 1, x_803);
x_805 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_779);
x_806 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_806, 0, x_779);
lean_ctor_set(x_806, 1, x_805);
x_807 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_779);
x_808 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_808, 0, x_779);
lean_ctor_set(x_808, 1, x_807);
x_809 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_779);
x_810 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_810, 0, x_779);
lean_ctor_set(x_810, 1, x_809);
lean_inc(x_779);
x_811 = l_Lean_Syntax_node5(x_779, x_802, x_804, x_806, x_808, x_801, x_810);
x_812 = l_Array_mkArray1___redArg(x_811);
x_160 = x_779;
x_161 = x_780;
x_162 = x_781;
x_163 = x_782;
x_164 = x_783;
x_165 = x_784;
x_166 = x_785;
x_167 = x_786;
x_168 = x_788;
x_169 = x_787;
x_170 = x_789;
x_171 = x_800;
x_172 = x_792;
x_173 = x_791;
x_174 = x_790;
x_175 = x_793;
x_176 = x_794;
x_177 = x_795;
x_178 = x_797;
x_179 = x_812;
goto block_217;
}
else
{
lean_object* x_813; 
lean_dec(x_796);
x_813 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_160 = x_779;
x_161 = x_780;
x_162 = x_781;
x_163 = x_782;
x_164 = x_783;
x_165 = x_784;
x_166 = x_785;
x_167 = x_786;
x_168 = x_788;
x_169 = x_787;
x_170 = x_789;
x_171 = x_800;
x_172 = x_792;
x_173 = x_791;
x_174 = x_790;
x_175 = x_793;
x_176 = x_794;
x_177 = x_795;
x_178 = x_797;
x_179 = x_813;
goto block_217;
}
}
block_856:
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_inc_ref(x_828);
x_834 = l_Array_append___redArg(x_828, x_833);
lean_dec_ref(x_833);
lean_inc(x_826);
lean_inc(x_815);
x_835 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_835, 0, x_815);
lean_ctor_set(x_835, 1, x_826);
lean_ctor_set(x_835, 2, x_834);
lean_inc_ref(x_828);
lean_inc(x_826);
lean_inc(x_815);
x_836 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_836, 0, x_815);
lean_ctor_set(x_836, 1, x_826);
lean_ctor_set(x_836, 2, x_828);
lean_inc(x_815);
x_837 = l_Lean_Syntax_node1(x_815, x_822, x_836);
lean_inc(x_815);
x_838 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_838, 0, x_815);
lean_ctor_set(x_838, 1, x_816);
x_839 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(x_815);
x_840 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_840, 0, x_815);
lean_ctor_set(x_840, 1, x_839);
lean_inc_ref(x_840);
lean_inc(x_821);
lean_inc(x_815);
x_841 = l_Lean_Syntax_node2(x_815, x_821, x_840, x_832);
lean_inc(x_826);
lean_inc(x_815);
x_842 = l_Lean_Syntax_node1(x_815, x_826, x_841);
if (lean_obj_tag(x_827) == 1)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_843 = lean_ctor_get(x_827, 0);
lean_inc(x_843);
lean_dec_ref(x_827);
x_844 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
x_845 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_815);
x_846 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_846, 0, x_815);
lean_ctor_set(x_846, 1, x_845);
x_847 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_815);
x_848 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_848, 0, x_815);
lean_ctor_set(x_848, 1, x_847);
x_849 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_815);
x_850 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_850, 0, x_815);
lean_ctor_set(x_850, 1, x_849);
x_851 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_815);
x_852 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_852, 0, x_815);
lean_ctor_set(x_852, 1, x_851);
lean_inc(x_815);
x_853 = l_Lean_Syntax_node5(x_815, x_844, x_846, x_848, x_850, x_843, x_852);
x_854 = l_Array_mkArray1___redArg(x_853);
x_779 = x_815;
x_780 = x_817;
x_781 = x_818;
x_782 = x_819;
x_783 = x_820;
x_784 = x_821;
x_785 = x_823;
x_786 = x_824;
x_787 = x_826;
x_788 = x_825;
x_789 = x_840;
x_790 = x_835;
x_791 = x_838;
x_792 = x_842;
x_793 = x_837;
x_794 = x_828;
x_795 = x_829;
x_796 = x_830;
x_797 = x_831;
x_798 = x_854;
goto block_814;
}
else
{
lean_object* x_855; 
lean_dec(x_827);
x_855 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_779 = x_815;
x_780 = x_817;
x_781 = x_818;
x_782 = x_819;
x_783 = x_820;
x_784 = x_821;
x_785 = x_823;
x_786 = x_824;
x_787 = x_826;
x_788 = x_825;
x_789 = x_840;
x_790 = x_835;
x_791 = x_838;
x_792 = x_842;
x_793 = x_837;
x_794 = x_828;
x_795 = x_829;
x_796 = x_830;
x_797 = x_831;
x_798 = x_855;
goto block_814;
}
}
block_890:
{
lean_object* x_876; lean_object* x_877; 
lean_inc_ref(x_870);
x_876 = l_Array_append___redArg(x_870, x_875);
lean_dec_ref(x_875);
lean_inc(x_867);
lean_inc(x_857);
x_877 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_877, 0, x_857);
lean_ctor_set(x_877, 1, x_867);
lean_ctor_set(x_877, 2, x_876);
if (lean_obj_tag(x_862) == 1)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_878 = lean_ctor_get(x_862, 0);
lean_inc(x_878);
lean_dec_ref(x_862);
x_879 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(x_873);
x_880 = l_Lean_Name_mkStr4(x_4, x_5, x_873, x_879);
x_881 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(x_857);
x_882 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_882, 0, x_857);
lean_ctor_set(x_882, 1, x_881);
lean_inc_ref(x_870);
x_883 = l_Array_append___redArg(x_870, x_878);
lean_dec(x_878);
lean_inc(x_867);
lean_inc(x_857);
x_884 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_884, 0, x_857);
lean_ctor_set(x_884, 1, x_867);
lean_ctor_set(x_884, 2, x_883);
x_885 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_857);
x_886 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_886, 0, x_857);
lean_ctor_set(x_886, 1, x_885);
lean_inc(x_857);
x_887 = l_Lean_Syntax_node3(x_857, x_880, x_882, x_884, x_886);
x_888 = l_Array_mkArray1___redArg(x_887);
x_815 = x_857;
x_816 = x_858;
x_817 = x_859;
x_818 = x_860;
x_819 = x_861;
x_820 = x_877;
x_821 = x_863;
x_822 = x_864;
x_823 = x_865;
x_824 = x_866;
x_825 = x_868;
x_826 = x_867;
x_827 = x_869;
x_828 = x_870;
x_829 = x_871;
x_830 = x_872;
x_831 = x_873;
x_832 = x_874;
x_833 = x_888;
goto block_856;
}
else
{
lean_object* x_889; 
lean_dec(x_862);
x_889 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_815 = x_857;
x_816 = x_858;
x_817 = x_859;
x_818 = x_860;
x_819 = x_861;
x_820 = x_877;
x_821 = x_863;
x_822 = x_864;
x_823 = x_865;
x_824 = x_866;
x_825 = x_868;
x_826 = x_867;
x_827 = x_869;
x_828 = x_870;
x_829 = x_871;
x_830 = x_872;
x_831 = x_873;
x_832 = x_874;
x_833 = x_889;
goto block_856;
}
}
block_934:
{
lean_object* x_903; 
lean_inc_ref(x_901);
lean_inc(x_897);
x_903 = l_Lean_evalPrec(x_897, x_901, x_902);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_903, 1);
lean_inc(x_905);
lean_dec_ref(x_903);
x_906 = lean_ctor_get(x_901, 1);
lean_inc(x_906);
x_907 = lean_ctor_get(x_901, 2);
lean_inc(x_907);
x_908 = lean_ctor_get(x_901, 5);
lean_inc(x_908);
lean_dec_ref(x_901);
x_909 = lean_unsigned_to_nat(7u);
x_910 = l_Lean_Syntax_getArg(x_1, x_909);
x_911 = lean_unsigned_to_nat(9u);
x_912 = l_Lean_Syntax_getArg(x_1, x_911);
lean_dec(x_1);
x_913 = lean_nat_add(x_904, x_899);
lean_dec(x_904);
x_914 = l_Nat_reprFast(x_913);
x_915 = lean_box(2);
x_916 = l_Lean_Syntax_mkNumLit(x_914, x_915);
x_917 = l_Lean_SourceInfo_fromRef(x_908, x_898);
lean_dec(x_908);
x_918 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
x_919 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_920 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
x_921 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(x_891) == 1)
{
lean_object* x_922; lean_object* x_923; 
x_922 = lean_ctor_get(x_891, 0);
lean_inc(x_922);
lean_dec_ref(x_891);
x_923 = l_Array_mkArray1___redArg(x_922);
x_857 = x_917;
x_858 = x_918;
x_859 = x_912;
x_860 = x_919;
x_861 = x_916;
x_862 = x_893;
x_863 = x_894;
x_864 = x_895;
x_865 = x_910;
x_866 = x_906;
x_867 = x_920;
x_868 = x_905;
x_869 = x_892;
x_870 = x_921;
x_871 = x_907;
x_872 = x_900;
x_873 = x_896;
x_874 = x_897;
x_875 = x_923;
goto block_890;
}
else
{
lean_object* x_924; 
lean_dec(x_891);
x_924 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_857 = x_917;
x_858 = x_918;
x_859 = x_912;
x_860 = x_919;
x_861 = x_916;
x_862 = x_893;
x_863 = x_894;
x_864 = x_895;
x_865 = x_910;
x_866 = x_906;
x_867 = x_920;
x_868 = x_905;
x_869 = x_892;
x_870 = x_921;
x_871 = x_907;
x_872 = x_900;
x_873 = x_896;
x_874 = x_897;
x_875 = x_924;
goto block_890;
}
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; uint8_t x_928; uint8_t x_933; 
lean_dec_ref(x_901);
lean_dec(x_900);
lean_dec(x_897);
lean_dec_ref(x_896);
lean_dec(x_895);
lean_dec(x_894);
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_1);
x_925 = lean_ctor_get(x_903, 0);
x_926 = lean_ctor_get(x_903, 1);
x_933 = !lean_is_exclusive(x_903);
if (x_933 == 0)
{
x_927 = x_903;
x_928 = x_933;
goto block_932;
}
else
{
lean_inc(x_926);
lean_inc(x_925);
lean_dec(x_903);
x_927 = lean_box(0);
x_928 = x_933;
goto block_932;
}
block_932:
{
lean_object* x_929; 
if (x_928 == 0)
{
x_929 = x_927;
goto block_930;
}
else
{
lean_object* x_931; 
x_931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_931, 0, x_925);
lean_ctor_set(x_931, 1, x_926);
x_929 = x_931;
goto block_930;
}
block_930:
{
return x_929;
}
}
}
}
block_959:
{
lean_object* x_947; lean_object* x_948; uint8_t x_949; 
x_947 = lean_unsigned_to_nat(6u);
x_948 = l_Lean_Syntax_getArg(x_1, x_947);
x_949 = l_Lean_Syntax_isNone(x_948);
if (x_949 == 0)
{
uint8_t x_950; 
lean_inc(x_948);
x_950 = l_Lean_Syntax_matchesNull(x_948, x_942);
if (x_950 == 0)
{
lean_object* x_951; 
lean_dec(x_948);
lean_dec_ref(x_945);
lean_dec(x_944);
lean_dec(x_941);
lean_dec_ref(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_937);
lean_dec(x_935);
lean_dec(x_1);
x_951 = l_Lean_Macro_throwUnsupported___redArg(x_946);
return x_951;
}
else
{
lean_object* x_952; lean_object* x_953; uint8_t x_954; 
x_952 = l_Lean_Syntax_getArg(x_948, x_279);
lean_dec(x_948);
x_953 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(x_952);
x_954 = l_Lean_Syntax_isOfKind(x_952, x_953);
if (x_954 == 0)
{
lean_object* x_955; 
lean_dec(x_952);
lean_dec_ref(x_945);
lean_dec(x_944);
lean_dec(x_941);
lean_dec_ref(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_937);
lean_dec(x_935);
lean_dec(x_1);
x_955 = l_Lean_Macro_throwUnsupported___redArg(x_946);
return x_955;
}
else
{
lean_object* x_956; lean_object* x_957; 
x_956 = l_Lean_Syntax_getArg(x_952, x_936);
lean_dec(x_952);
x_957 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_957, 0, x_956);
x_891 = x_935;
x_892 = x_944;
x_893 = x_937;
x_894 = x_938;
x_895 = x_939;
x_896 = x_940;
x_897 = x_941;
x_898 = x_943;
x_899 = x_942;
x_900 = x_957;
x_901 = x_945;
x_902 = x_946;
goto block_934;
}
}
}
else
{
lean_object* x_958; 
lean_dec(x_948);
x_958 = lean_box(0);
x_891 = x_935;
x_892 = x_944;
x_893 = x_937;
x_894 = x_938;
x_895 = x_939;
x_896 = x_940;
x_897 = x_941;
x_898 = x_943;
x_899 = x_942;
x_900 = x_958;
x_901 = x_945;
x_902 = x_946;
goto block_934;
}
}
block_995:
{
lean_object* x_980; lean_object* x_981; 
lean_inc_ref(x_964);
x_980 = l_Array_append___redArg(x_964, x_979);
lean_dec_ref(x_979);
lean_inc(x_976);
lean_inc(x_967);
x_981 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_981, 0, x_967);
lean_ctor_set(x_981, 1, x_976);
lean_ctor_set(x_981, 2, x_980);
if (lean_obj_tag(x_974) == 1)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_982 = lean_ctor_get(x_974, 0);
lean_inc(x_982);
lean_dec_ref(x_974);
x_983 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
x_984 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_967);
x_985 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_985, 0, x_967);
lean_ctor_set(x_985, 1, x_984);
x_986 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_967);
x_987 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_987, 0, x_967);
lean_ctor_set(x_987, 1, x_986);
x_988 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_967);
x_989 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_989, 0, x_967);
lean_ctor_set(x_989, 1, x_988);
x_990 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_967);
x_991 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_991, 0, x_967);
lean_ctor_set(x_991, 1, x_990);
lean_inc(x_967);
x_992 = l_Lean_Syntax_node5(x_967, x_983, x_985, x_987, x_989, x_982, x_991);
x_993 = l_Array_mkArray1___redArg(x_992);
x_218 = x_960;
x_219 = x_961;
x_220 = x_962;
x_221 = x_963;
x_222 = x_964;
x_223 = x_965;
x_224 = x_981;
x_225 = x_966;
x_226 = x_967;
x_227 = x_968;
x_228 = x_971;
x_229 = x_972;
x_230 = x_973;
x_231 = x_970;
x_232 = x_969;
x_233 = x_975;
x_234 = x_976;
x_235 = x_977;
x_236 = x_978;
x_237 = x_993;
goto block_275;
}
else
{
lean_object* x_994; 
lean_dec(x_974);
x_994 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_218 = x_960;
x_219 = x_961;
x_220 = x_962;
x_221 = x_963;
x_222 = x_964;
x_223 = x_965;
x_224 = x_981;
x_225 = x_966;
x_226 = x_967;
x_227 = x_968;
x_228 = x_971;
x_229 = x_972;
x_230 = x_973;
x_231 = x_970;
x_232 = x_969;
x_233 = x_975;
x_234 = x_976;
x_235 = x_977;
x_236 = x_978;
x_237 = x_994;
goto block_275;
}
}
block_1037:
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
lean_inc_ref(x_1002);
x_1015 = l_Array_append___redArg(x_1002, x_1014);
lean_dec_ref(x_1014);
lean_inc(x_1011);
lean_inc(x_1005);
x_1016 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1016, 0, x_1005);
lean_ctor_set(x_1016, 1, x_1011);
lean_ctor_set(x_1016, 2, x_1015);
lean_inc_ref(x_1002);
lean_inc(x_1011);
lean_inc(x_1005);
x_1017 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1017, 0, x_1005);
lean_ctor_set(x_1017, 1, x_1011);
lean_ctor_set(x_1017, 2, x_1002);
lean_inc(x_1005);
x_1018 = l_Lean_Syntax_node1(x_1005, x_1001, x_1017);
lean_inc(x_1005);
x_1019 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1019, 0, x_1005);
lean_ctor_set(x_1019, 1, x_997);
x_1020 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25));
lean_inc(x_1005);
x_1021 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1021, 0, x_1005);
lean_ctor_set(x_1021, 1, x_1020);
lean_inc_ref(x_1021);
lean_inc(x_1007);
lean_inc(x_1005);
x_1022 = l_Lean_Syntax_node2(x_1005, x_1007, x_1021, x_1003);
lean_inc(x_1011);
lean_inc(x_1005);
x_1023 = l_Lean_Syntax_node1(x_1005, x_1011, x_1022);
if (lean_obj_tag(x_1006) == 1)
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1024 = lean_ctor_get(x_1006, 0);
lean_inc(x_1024);
lean_dec_ref(x_1006);
x_1025 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
x_1026 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_1005);
x_1027 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1027, 0, x_1005);
lean_ctor_set(x_1027, 1, x_1026);
x_1028 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_1005);
x_1029 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1029, 0, x_1005);
lean_ctor_set(x_1029, 1, x_1028);
x_1030 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_1005);
x_1031 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1031, 0, x_1005);
lean_ctor_set(x_1031, 1, x_1030);
x_1032 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_1005);
x_1033 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1033, 0, x_1005);
lean_ctor_set(x_1033, 1, x_1032);
lean_inc(x_1005);
x_1034 = l_Lean_Syntax_node5(x_1005, x_1025, x_1027, x_1029, x_1031, x_1024, x_1033);
x_1035 = l_Array_mkArray1___redArg(x_1034);
x_960 = x_996;
x_961 = x_998;
x_962 = x_999;
x_963 = x_1000;
x_964 = x_1002;
x_965 = x_1021;
x_966 = x_1004;
x_967 = x_1005;
x_968 = x_1007;
x_969 = x_1009;
x_970 = x_1016;
x_971 = x_1008;
x_972 = x_1019;
x_973 = x_1018;
x_974 = x_1010;
x_975 = x_1023;
x_976 = x_1011;
x_977 = x_1012;
x_978 = x_1013;
x_979 = x_1035;
goto block_995;
}
else
{
lean_object* x_1036; 
lean_dec(x_1006);
x_1036 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_960 = x_996;
x_961 = x_998;
x_962 = x_999;
x_963 = x_1000;
x_964 = x_1002;
x_965 = x_1021;
x_966 = x_1004;
x_967 = x_1005;
x_968 = x_1007;
x_969 = x_1009;
x_970 = x_1016;
x_971 = x_1008;
x_972 = x_1019;
x_973 = x_1018;
x_974 = x_1010;
x_975 = x_1023;
x_976 = x_1011;
x_977 = x_1012;
x_978 = x_1013;
x_979 = x_1036;
goto block_995;
}
}
block_1071:
{
lean_object* x_1057; lean_object* x_1058; 
lean_inc_ref(x_1045);
x_1057 = l_Array_append___redArg(x_1045, x_1056);
lean_dec_ref(x_1056);
lean_inc(x_1053);
lean_inc(x_1048);
x_1058 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1058, 0, x_1048);
lean_ctor_set(x_1058, 1, x_1053);
lean_ctor_set(x_1058, 2, x_1057);
if (lean_obj_tag(x_1041) == 1)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1059 = lean_ctor_get(x_1041, 0);
lean_inc(x_1059);
lean_dec_ref(x_1041);
x_1060 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc_ref(x_1054);
x_1061 = l_Lean_Name_mkStr4(x_4, x_5, x_1054, x_1060);
x_1062 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc(x_1048);
x_1063 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1063, 0, x_1048);
lean_ctor_set(x_1063, 1, x_1062);
lean_inc_ref(x_1045);
x_1064 = l_Array_append___redArg(x_1045, x_1059);
lean_dec(x_1059);
lean_inc(x_1053);
lean_inc(x_1048);
x_1065 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1065, 0, x_1048);
lean_ctor_set(x_1065, 1, x_1053);
lean_ctor_set(x_1065, 2, x_1064);
x_1066 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_1048);
x_1067 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1067, 0, x_1048);
lean_ctor_set(x_1067, 1, x_1066);
lean_inc(x_1048);
x_1068 = l_Lean_Syntax_node3(x_1048, x_1061, x_1063, x_1065, x_1067);
x_1069 = l_Array_mkArray1___redArg(x_1068);
x_996 = x_1038;
x_997 = x_1039;
x_998 = x_1040;
x_999 = x_1042;
x_1000 = x_1043;
x_1001 = x_1044;
x_1002 = x_1045;
x_1003 = x_1046;
x_1004 = x_1047;
x_1005 = x_1048;
x_1006 = x_1049;
x_1007 = x_1050;
x_1008 = x_1051;
x_1009 = x_1058;
x_1010 = x_1052;
x_1011 = x_1053;
x_1012 = x_1054;
x_1013 = x_1055;
x_1014 = x_1069;
goto block_1037;
}
else
{
lean_object* x_1070; 
lean_dec(x_1041);
x_1070 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_996 = x_1038;
x_997 = x_1039;
x_998 = x_1040;
x_999 = x_1042;
x_1000 = x_1043;
x_1001 = x_1044;
x_1002 = x_1045;
x_1003 = x_1046;
x_1004 = x_1047;
x_1005 = x_1048;
x_1006 = x_1049;
x_1007 = x_1050;
x_1008 = x_1051;
x_1009 = x_1058;
x_1010 = x_1052;
x_1011 = x_1053;
x_1012 = x_1054;
x_1013 = x_1055;
x_1014 = x_1070;
goto block_1037;
}
}
block_1115:
{
lean_object* x_1083; 
lean_inc_ref(x_1081);
lean_inc(x_1072);
x_1083 = l_Lean_evalPrec(x_1072, x_1081, x_1082);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
lean_dec_ref(x_1083);
x_1086 = lean_ctor_get(x_1081, 1);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1081, 2);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1081, 5);
lean_inc(x_1088);
lean_dec_ref(x_1081);
x_1089 = lean_unsigned_to_nat(7u);
x_1090 = l_Lean_Syntax_getArg(x_1, x_1089);
x_1091 = lean_unsigned_to_nat(9u);
x_1092 = l_Lean_Syntax_getArg(x_1, x_1091);
lean_dec(x_1);
x_1093 = lean_nat_add(x_1084, x_1079);
lean_dec(x_1084);
x_1094 = l_Nat_reprFast(x_1093);
x_1095 = lean_box(2);
x_1096 = l_Lean_Syntax_mkNumLit(x_1094, x_1095);
x_1097 = 0;
x_1098 = l_Lean_SourceInfo_fromRef(x_1088, x_1097);
lean_dec(x_1088);
x_1099 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
x_1100 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_1101 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35));
x_1102 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36);
if (lean_obj_tag(x_1073) == 1)
{
lean_object* x_1103; lean_object* x_1104; 
x_1103 = lean_ctor_get(x_1073, 0);
lean_inc(x_1103);
lean_dec_ref(x_1073);
x_1104 = l_Array_mkArray1___redArg(x_1103);
x_1038 = x_1096;
x_1039 = x_1099;
x_1040 = x_1090;
x_1041 = x_1076;
x_1042 = x_1087;
x_1043 = x_1085;
x_1044 = x_1077;
x_1045 = x_1102;
x_1046 = x_1072;
x_1047 = x_1086;
x_1048 = x_1098;
x_1049 = x_1075;
x_1050 = x_1074;
x_1051 = x_1100;
x_1052 = x_1080;
x_1053 = x_1101;
x_1054 = x_1078;
x_1055 = x_1092;
x_1056 = x_1104;
goto block_1071;
}
else
{
lean_object* x_1105; 
lean_dec(x_1073);
x_1105 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
x_1038 = x_1096;
x_1039 = x_1099;
x_1040 = x_1090;
x_1041 = x_1076;
x_1042 = x_1087;
x_1043 = x_1085;
x_1044 = x_1077;
x_1045 = x_1102;
x_1046 = x_1072;
x_1047 = x_1086;
x_1048 = x_1098;
x_1049 = x_1075;
x_1050 = x_1074;
x_1051 = x_1100;
x_1052 = x_1080;
x_1053 = x_1101;
x_1054 = x_1078;
x_1055 = x_1092;
x_1056 = x_1105;
goto block_1071;
}
}
else
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; uint8_t x_1109; uint8_t x_1114; 
lean_dec_ref(x_1081);
lean_dec(x_1080);
lean_dec_ref(x_1078);
lean_dec(x_1077);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_1);
x_1106 = lean_ctor_get(x_1083, 0);
x_1107 = lean_ctor_get(x_1083, 1);
x_1114 = !lean_is_exclusive(x_1083);
if (x_1114 == 0)
{
x_1108 = x_1083;
x_1109 = x_1114;
goto block_1113;
}
else
{
lean_inc(x_1107);
lean_inc(x_1106);
lean_dec(x_1083);
x_1108 = lean_box(0);
x_1109 = x_1114;
goto block_1113;
}
block_1113:
{
lean_object* x_1110; 
if (x_1109 == 0)
{
x_1110 = x_1108;
goto block_1111;
}
else
{
lean_object* x_1112; 
x_1112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1112, 0, x_1106);
lean_ctor_set(x_1112, 1, x_1107);
x_1110 = x_1112;
goto block_1111;
}
block_1111:
{
return x_1110;
}
}
}
}
block_1139:
{
lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; 
x_1127 = lean_unsigned_to_nat(6u);
x_1128 = l_Lean_Syntax_getArg(x_1, x_1127);
x_1129 = l_Lean_Syntax_isNone(x_1128);
if (x_1129 == 0)
{
uint8_t x_1130; 
lean_inc(x_1128);
x_1130 = l_Lean_Syntax_matchesNull(x_1128, x_1123);
if (x_1130 == 0)
{
lean_object* x_1131; 
lean_dec(x_1128);
lean_dec_ref(x_1125);
lean_dec(x_1124);
lean_dec_ref(x_1122);
lean_dec(x_1121);
lean_dec(x_1120);
lean_dec(x_1119);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1);
x_1131 = l_Lean_Macro_throwUnsupported___redArg(x_1126);
return x_1131;
}
else
{
lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; 
x_1132 = l_Lean_Syntax_getArg(x_1128, x_279);
lean_dec(x_1128);
x_1133 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19));
lean_inc(x_1132);
x_1134 = l_Lean_Syntax_isOfKind(x_1132, x_1133);
if (x_1134 == 0)
{
lean_object* x_1135; 
lean_dec(x_1132);
lean_dec_ref(x_1125);
lean_dec(x_1124);
lean_dec_ref(x_1122);
lean_dec(x_1121);
lean_dec(x_1120);
lean_dec(x_1119);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1);
x_1135 = l_Lean_Macro_throwUnsupported___redArg(x_1126);
return x_1135;
}
else
{
lean_object* x_1136; lean_object* x_1137; 
x_1136 = l_Lean_Syntax_getArg(x_1132, x_1118);
lean_dec(x_1132);
x_1137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1137, 0, x_1136);
x_1072 = x_1116;
x_1073 = x_1117;
x_1074 = x_1119;
x_1075 = x_1124;
x_1076 = x_1120;
x_1077 = x_1121;
x_1078 = x_1122;
x_1079 = x_1123;
x_1080 = x_1137;
x_1081 = x_1125;
x_1082 = x_1126;
goto block_1115;
}
}
}
else
{
lean_object* x_1138; 
lean_dec(x_1128);
x_1138 = lean_box(0);
x_1072 = x_1116;
x_1073 = x_1117;
x_1074 = x_1119;
x_1075 = x_1124;
x_1076 = x_1120;
x_1077 = x_1121;
x_1078 = x_1122;
x_1079 = x_1123;
x_1080 = x_1138;
x_1081 = x_1125;
x_1082 = x_1126;
goto block_1115;
}
}
block_1257:
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; uint8_t x_1149; 
x_1145 = lean_unsigned_to_nat(2u);
x_1146 = l_Lean_Syntax_getArg(x_1, x_1145);
x_1147 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37));
x_1148 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39));
lean_inc(x_1146);
x_1149 = l_Lean_Syntax_isOfKind(x_1146, x_1148);
if (x_1149 == 0)
{
lean_object* x_1150; 
lean_dec(x_1146);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1150 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1150;
}
else
{
lean_object* x_1151; uint8_t x_1152; 
x_1151 = l_Lean_Syntax_getArg(x_1146, x_279);
lean_dec(x_1146);
x_1152 = l_Lean_Syntax_matchesNull(x_1151, x_279);
if (x_1152 == 0)
{
lean_object* x_1153; 
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1153 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1153;
}
else
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; uint8_t x_1157; 
x_1154 = lean_unsigned_to_nat(3u);
x_1155 = l_Lean_Syntax_getArg(x_1, x_1154);
x_1156 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41));
lean_inc(x_1155);
x_1157 = l_Lean_Syntax_isOfKind(x_1155, x_1156);
if (x_1157 == 0)
{
lean_object* x_1158; uint8_t x_1159; 
x_1158 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43));
lean_inc(x_1155);
x_1159 = l_Lean_Syntax_isOfKind(x_1155, x_1158);
if (x_1159 == 0)
{
lean_object* x_1160; uint8_t x_1161; 
x_1160 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45));
lean_inc(x_1155);
x_1161 = l_Lean_Syntax_isOfKind(x_1155, x_1160);
if (x_1161 == 0)
{
lean_object* x_1162; uint8_t x_1163; 
x_1162 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47));
lean_inc(x_1155);
x_1163 = l_Lean_Syntax_isOfKind(x_1155, x_1162);
if (x_1163 == 0)
{
lean_object* x_1164; uint8_t x_1165; 
x_1164 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49));
x_1165 = l_Lean_Syntax_isOfKind(x_1155, x_1164);
if (x_1165 == 0)
{
lean_object* x_1166; 
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1166 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1166;
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; uint8_t x_1170; 
x_1167 = lean_unsigned_to_nat(4u);
x_1168 = l_Lean_Syntax_getArg(x_1, x_1167);
x_1169 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(x_1168);
x_1170 = l_Lean_Syntax_isOfKind(x_1168, x_1169);
if (x_1170 == 0)
{
lean_object* x_1171; 
lean_dec(x_1168);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1171 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1171;
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; 
x_1172 = l_Lean_Syntax_getArg(x_1168, x_1141);
lean_dec(x_1168);
x_1173 = lean_unsigned_to_nat(5u);
x_1174 = l_Lean_Syntax_getArg(x_1, x_1173);
x_1175 = l_Lean_Syntax_isNone(x_1174);
if (x_1175 == 0)
{
uint8_t x_1176; 
lean_inc(x_1174);
x_1176 = l_Lean_Syntax_matchesNull(x_1174, x_1141);
if (x_1176 == 0)
{
lean_object* x_1177; 
lean_dec(x_1174);
lean_dec(x_1172);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1177 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1177;
}
else
{
lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; 
x_1178 = l_Lean_Syntax_getArg(x_1174, x_279);
lean_dec(x_1174);
x_1179 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(x_1178);
x_1180 = l_Lean_Syntax_isOfKind(x_1178, x_1179);
if (x_1180 == 0)
{
lean_object* x_1181; 
lean_dec(x_1178);
lean_dec(x_1172);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1181 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1181;
}
else
{
lean_object* x_1182; lean_object* x_1183; 
x_1182 = l_Lean_Syntax_getArg(x_1178, x_1154);
lean_dec(x_1178);
x_1183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1183, 0, x_1182);
x_414 = x_1140;
x_415 = x_1163;
x_416 = x_1169;
x_417 = x_1172;
x_418 = x_1154;
x_419 = x_1142;
x_420 = x_1148;
x_421 = x_1147;
x_422 = x_1141;
x_423 = x_1183;
x_424 = x_1143;
x_425 = x_1144;
goto block_438;
}
}
}
else
{
lean_object* x_1184; 
lean_dec(x_1174);
x_1184 = lean_box(0);
x_414 = x_1140;
x_415 = x_1163;
x_416 = x_1169;
x_417 = x_1172;
x_418 = x_1154;
x_419 = x_1142;
x_420 = x_1148;
x_421 = x_1147;
x_422 = x_1141;
x_423 = x_1184;
x_424 = x_1143;
x_425 = x_1144;
goto block_438;
}
}
}
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; uint8_t x_1188; 
lean_dec(x_1155);
x_1185 = lean_unsigned_to_nat(4u);
x_1186 = l_Lean_Syntax_getArg(x_1, x_1185);
x_1187 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(x_1186);
x_1188 = l_Lean_Syntax_isOfKind(x_1186, x_1187);
if (x_1188 == 0)
{
lean_object* x_1189; 
lean_dec(x_1186);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1189 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1189;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; uint8_t x_1193; 
x_1190 = l_Lean_Syntax_getArg(x_1186, x_1141);
lean_dec(x_1186);
x_1191 = lean_unsigned_to_nat(5u);
x_1192 = l_Lean_Syntax_getArg(x_1, x_1191);
x_1193 = l_Lean_Syntax_isNone(x_1192);
if (x_1193 == 0)
{
uint8_t x_1194; 
lean_inc(x_1192);
x_1194 = l_Lean_Syntax_matchesNull(x_1192, x_1141);
if (x_1194 == 0)
{
lean_object* x_1195; 
lean_dec(x_1192);
lean_dec(x_1190);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1195 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1195;
}
else
{
lean_object* x_1196; lean_object* x_1197; uint8_t x_1198; 
x_1196 = l_Lean_Syntax_getArg(x_1192, x_279);
lean_dec(x_1192);
x_1197 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(x_1196);
x_1198 = l_Lean_Syntax_isOfKind(x_1196, x_1197);
if (x_1198 == 0)
{
lean_object* x_1199; 
lean_dec(x_1196);
lean_dec(x_1190);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1199 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1199;
}
else
{
lean_object* x_1200; lean_object* x_1201; 
x_1200 = l_Lean_Syntax_getArg(x_1196, x_1154);
lean_dec(x_1196);
x_1201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1201, 0, x_1200);
x_573 = x_1187;
x_574 = x_1140;
x_575 = x_1154;
x_576 = x_1142;
x_577 = x_1161;
x_578 = x_1148;
x_579 = x_1190;
x_580 = x_1147;
x_581 = x_1141;
x_582 = x_1201;
x_583 = x_1143;
x_584 = x_1144;
goto block_597;
}
}
}
else
{
lean_object* x_1202; 
lean_dec(x_1192);
x_1202 = lean_box(0);
x_573 = x_1187;
x_574 = x_1140;
x_575 = x_1154;
x_576 = x_1142;
x_577 = x_1161;
x_578 = x_1148;
x_579 = x_1190;
x_580 = x_1147;
x_581 = x_1141;
x_582 = x_1202;
x_583 = x_1143;
x_584 = x_1144;
goto block_597;
}
}
}
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; uint8_t x_1206; 
lean_dec(x_1155);
x_1203 = lean_unsigned_to_nat(4u);
x_1204 = l_Lean_Syntax_getArg(x_1, x_1203);
x_1205 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(x_1204);
x_1206 = l_Lean_Syntax_isOfKind(x_1204, x_1205);
if (x_1206 == 0)
{
lean_object* x_1207; 
lean_dec(x_1204);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1207 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1207;
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; uint8_t x_1211; 
x_1208 = l_Lean_Syntax_getArg(x_1204, x_1141);
lean_dec(x_1204);
x_1209 = lean_unsigned_to_nat(5u);
x_1210 = l_Lean_Syntax_getArg(x_1, x_1209);
x_1211 = l_Lean_Syntax_isNone(x_1210);
if (x_1211 == 0)
{
uint8_t x_1212; 
lean_inc(x_1210);
x_1212 = l_Lean_Syntax_matchesNull(x_1210, x_1141);
if (x_1212 == 0)
{
lean_object* x_1213; 
lean_dec(x_1210);
lean_dec(x_1208);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1213 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1213;
}
else
{
lean_object* x_1214; lean_object* x_1215; uint8_t x_1216; 
x_1214 = l_Lean_Syntax_getArg(x_1210, x_279);
lean_dec(x_1210);
x_1215 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(x_1214);
x_1216 = l_Lean_Syntax_isOfKind(x_1214, x_1215);
if (x_1216 == 0)
{
lean_object* x_1217; 
lean_dec(x_1214);
lean_dec(x_1208);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1217 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1217;
}
else
{
lean_object* x_1218; lean_object* x_1219; 
x_1218 = l_Lean_Syntax_getArg(x_1214, x_1154);
lean_dec(x_1214);
x_1219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1219, 0, x_1218);
x_754 = x_1140;
x_755 = x_1159;
x_756 = x_1208;
x_757 = x_1154;
x_758 = x_1142;
x_759 = x_1148;
x_760 = x_1205;
x_761 = x_1147;
x_762 = x_1141;
x_763 = x_1219;
x_764 = x_1143;
x_765 = x_1144;
goto block_778;
}
}
}
else
{
lean_object* x_1220; 
lean_dec(x_1210);
x_1220 = lean_box(0);
x_754 = x_1140;
x_755 = x_1159;
x_756 = x_1208;
x_757 = x_1154;
x_758 = x_1142;
x_759 = x_1148;
x_760 = x_1205;
x_761 = x_1147;
x_762 = x_1141;
x_763 = x_1220;
x_764 = x_1143;
x_765 = x_1144;
goto block_778;
}
}
}
}
else
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; uint8_t x_1224; 
lean_dec(x_1155);
x_1221 = lean_unsigned_to_nat(4u);
x_1222 = l_Lean_Syntax_getArg(x_1, x_1221);
x_1223 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(x_1222);
x_1224 = l_Lean_Syntax_isOfKind(x_1222, x_1223);
if (x_1224 == 0)
{
lean_object* x_1225; 
lean_dec(x_1222);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1225 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1225;
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; uint8_t x_1229; 
x_1226 = l_Lean_Syntax_getArg(x_1222, x_1141);
lean_dec(x_1222);
x_1227 = lean_unsigned_to_nat(5u);
x_1228 = l_Lean_Syntax_getArg(x_1, x_1227);
x_1229 = l_Lean_Syntax_isNone(x_1228);
if (x_1229 == 0)
{
uint8_t x_1230; 
lean_inc(x_1228);
x_1230 = l_Lean_Syntax_matchesNull(x_1228, x_1141);
if (x_1230 == 0)
{
lean_object* x_1231; 
lean_dec(x_1228);
lean_dec(x_1226);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1231 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1231;
}
else
{
lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; 
x_1232 = l_Lean_Syntax_getArg(x_1228, x_279);
lean_dec(x_1228);
x_1233 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(x_1232);
x_1234 = l_Lean_Syntax_isOfKind(x_1232, x_1233);
if (x_1234 == 0)
{
lean_object* x_1235; 
lean_dec(x_1232);
lean_dec(x_1226);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1235 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1235;
}
else
{
lean_object* x_1236; lean_object* x_1237; 
x_1236 = l_Lean_Syntax_getArg(x_1232, x_1154);
lean_dec(x_1232);
x_1237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1237, 0, x_1236);
x_935 = x_1140;
x_936 = x_1154;
x_937 = x_1142;
x_938 = x_1223;
x_939 = x_1148;
x_940 = x_1147;
x_941 = x_1226;
x_942 = x_1141;
x_943 = x_1157;
x_944 = x_1237;
x_945 = x_1143;
x_946 = x_1144;
goto block_959;
}
}
}
else
{
lean_object* x_1238; 
lean_dec(x_1228);
x_1238 = lean_box(0);
x_935 = x_1140;
x_936 = x_1154;
x_937 = x_1142;
x_938 = x_1223;
x_939 = x_1148;
x_940 = x_1147;
x_941 = x_1226;
x_942 = x_1141;
x_943 = x_1157;
x_944 = x_1238;
x_945 = x_1143;
x_946 = x_1144;
goto block_959;
}
}
}
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; uint8_t x_1242; 
lean_dec(x_1155);
x_1239 = lean_unsigned_to_nat(4u);
x_1240 = l_Lean_Syntax_getArg(x_1, x_1239);
x_1241 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51));
lean_inc(x_1240);
x_1242 = l_Lean_Syntax_isOfKind(x_1240, x_1241);
if (x_1242 == 0)
{
lean_object* x_1243; 
lean_dec(x_1240);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1243 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1243;
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; uint8_t x_1247; 
x_1244 = l_Lean_Syntax_getArg(x_1240, x_1141);
lean_dec(x_1240);
x_1245 = lean_unsigned_to_nat(5u);
x_1246 = l_Lean_Syntax_getArg(x_1, x_1245);
x_1247 = l_Lean_Syntax_isNone(x_1246);
if (x_1247 == 0)
{
uint8_t x_1248; 
lean_inc(x_1246);
x_1248 = l_Lean_Syntax_matchesNull(x_1246, x_1141);
if (x_1248 == 0)
{
lean_object* x_1249; 
lean_dec(x_1246);
lean_dec(x_1244);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1249 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1249;
}
else
{
lean_object* x_1250; lean_object* x_1251; uint8_t x_1252; 
x_1250 = l_Lean_Syntax_getArg(x_1246, x_279);
lean_dec(x_1246);
x_1251 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27));
lean_inc(x_1250);
x_1252 = l_Lean_Syntax_isOfKind(x_1250, x_1251);
if (x_1252 == 0)
{
lean_object* x_1253; 
lean_dec(x_1250);
lean_dec(x_1244);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1);
x_1253 = l_Lean_Macro_throwUnsupported___redArg(x_1144);
return x_1253;
}
else
{
lean_object* x_1254; lean_object* x_1255; 
x_1254 = l_Lean_Syntax_getArg(x_1250, x_1154);
lean_dec(x_1250);
x_1255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1255, 0, x_1254);
x_1116 = x_1244;
x_1117 = x_1140;
x_1118 = x_1154;
x_1119 = x_1241;
x_1120 = x_1142;
x_1121 = x_1148;
x_1122 = x_1147;
x_1123 = x_1141;
x_1124 = x_1255;
x_1125 = x_1143;
x_1126 = x_1144;
goto block_1139;
}
}
}
else
{
lean_object* x_1256; 
lean_dec(x_1246);
x_1256 = lean_box(0);
x_1116 = x_1244;
x_1117 = x_1140;
x_1118 = x_1154;
x_1119 = x_1241;
x_1120 = x_1142;
x_1121 = x_1148;
x_1122 = x_1147;
x_1123 = x_1141;
x_1124 = x_1256;
x_1125 = x_1143;
x_1126 = x_1144;
goto block_1139;
}
}
}
}
}
}
block_1274:
{
lean_object* x_1261; lean_object* x_1262; uint8_t x_1263; 
x_1261 = lean_unsigned_to_nat(1u);
x_1262 = l_Lean_Syntax_getArg(x_1, x_1261);
x_1263 = l_Lean_Syntax_isNone(x_1262);
if (x_1263 == 0)
{
uint8_t x_1264; 
lean_inc(x_1262);
x_1264 = l_Lean_Syntax_matchesNull(x_1262, x_1261);
if (x_1264 == 0)
{
lean_object* x_1265; 
lean_dec(x_1262);
lean_dec_ref(x_1259);
lean_dec(x_1258);
lean_dec(x_1);
x_1265 = l_Lean_Macro_throwUnsupported___redArg(x_1260);
return x_1265;
}
else
{
lean_object* x_1266; lean_object* x_1267; uint8_t x_1268; 
x_1266 = l_Lean_Syntax_getArg(x_1262, x_279);
lean_dec(x_1262);
x_1267 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(x_1266);
x_1268 = l_Lean_Syntax_isOfKind(x_1266, x_1267);
if (x_1268 == 0)
{
lean_object* x_1269; 
lean_dec(x_1266);
lean_dec_ref(x_1259);
lean_dec(x_1258);
lean_dec(x_1);
x_1269 = l_Lean_Macro_throwUnsupported___redArg(x_1260);
return x_1269;
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1270 = l_Lean_Syntax_getArg(x_1266, x_1261);
lean_dec(x_1266);
x_1271 = l_Lean_Syntax_getArgs(x_1270);
lean_dec(x_1270);
x_1272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1272, 0, x_1271);
x_1140 = x_1258;
x_1141 = x_1261;
x_1142 = x_1272;
x_1143 = x_1259;
x_1144 = x_1260;
goto block_1257;
}
}
}
else
{
lean_object* x_1273; 
lean_dec(x_1262);
x_1273 = lean_box(0);
x_1140 = x_1258;
x_1141 = x_1261;
x_1142 = x_1273;
x_1143 = x_1259;
x_1144 = x_1260;
goto block_1257;
}
}
}
block_53:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_23 = l_Array_append___redArg(x_11, x_22);
lean_dec_ref(x_22);
lean_inc(x_14);
lean_inc(x_16);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_23);
x_25 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_26 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__6, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6);
x_27 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
x_28 = l_Lean_addMacroScope(x_12, x_27, x_21);
x_29 = lean_box(0);
lean_inc(x_16);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
lean_inc(x_17);
lean_inc_ref(x_30);
lean_inc(x_16);
x_31 = l_Lean_Syntax_node2(x_16, x_25, x_30, x_17);
lean_inc(x_14);
lean_inc(x_16);
x_32 = l_Lean_Syntax_node2(x_16, x_14, x_31, x_6);
x_33 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_16);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_33);
x_35 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_36 = l_Lean_Name_mkStr4(x_4, x_5, x_20, x_35);
lean_inc(x_16);
x_37 = l_Lean_Syntax_node1(x_16, x_14, x_30);
lean_inc(x_16);
x_38 = l_Lean_Syntax_node2(x_16, x_36, x_9, x_37);
x_39 = lean_unsigned_to_nat(10u);
x_40 = lean_mk_empty_array_with_capacity(x_39);
x_41 = lean_array_push(x_40, x_7);
x_42 = lean_array_push(x_41, x_10);
x_43 = lean_array_push(x_42, x_19);
x_44 = lean_array_push(x_43, x_13);
x_45 = lean_array_push(x_44, x_17);
x_46 = lean_array_push(x_45, x_18);
x_47 = lean_array_push(x_46, x_24);
x_48 = lean_array_push(x_47, x_32);
x_49 = lean_array_push(x_48, x_34);
x_50 = lean_array_push(x_49, x_38);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_8);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_15);
return x_52;
}
block_101:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_71 = l_Array_append___redArg(x_54, x_70);
lean_dec_ref(x_70);
lean_inc(x_63);
lean_inc(x_67);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_71);
x_73 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_74 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__6, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6);
x_75 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
x_76 = l_Lean_addMacroScope(x_68, x_75, x_55);
x_77 = lean_box(0);
lean_inc(x_67);
x_78 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_77);
lean_inc(x_57);
lean_inc_ref(x_78);
lean_inc(x_67);
x_79 = l_Lean_Syntax_node2(x_67, x_73, x_78, x_57);
lean_inc(x_63);
lean_inc(x_67);
x_80 = l_Lean_Syntax_node2(x_67, x_63, x_56, x_79);
x_81 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_67);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_84 = l_Lean_Name_mkStr4(x_4, x_5, x_69, x_83);
lean_inc(x_67);
x_85 = l_Lean_Syntax_node1(x_67, x_63, x_78);
lean_inc(x_67);
x_86 = l_Lean_Syntax_node2(x_67, x_84, x_62, x_85);
x_87 = lean_unsigned_to_nat(10u);
x_88 = lean_mk_empty_array_with_capacity(x_87);
x_89 = lean_array_push(x_88, x_65);
x_90 = lean_array_push(x_89, x_60);
x_91 = lean_array_push(x_90, x_66);
x_92 = lean_array_push(x_91, x_59);
x_93 = lean_array_push(x_92, x_57);
x_94 = lean_array_push(x_93, x_64);
x_95 = lean_array_push(x_94, x_72);
x_96 = lean_array_push(x_95, x_80);
x_97 = lean_array_push(x_96, x_82);
x_98 = lean_array_push(x_97, x_86);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_67);
lean_ctor_set(x_99, 1, x_58);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_61);
return x_100;
}
block_159:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_122 = l_Array_append___redArg(x_118, x_121);
lean_dec_ref(x_121);
lean_inc(x_114);
lean_inc(x_103);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_103);
lean_ctor_set(x_123, 1, x_114);
lean_ctor_set(x_123, 2, x_122);
x_124 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_125 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
x_126 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc(x_115);
lean_inc(x_106);
x_127 = l_Lean_addMacroScope(x_106, x_126, x_115);
x_128 = lean_box(0);
lean_inc(x_103);
x_129 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_129, 0, x_103);
lean_ctor_set(x_129, 1, x_125);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_128);
lean_inc(x_103);
x_130 = l_Lean_Syntax_node2(x_103, x_110, x_102, x_112);
lean_inc(x_114);
lean_inc(x_103);
x_131 = l_Lean_Syntax_node1(x_103, x_114, x_130);
lean_inc_ref(x_129);
lean_inc(x_103);
x_132 = l_Lean_Syntax_node2(x_103, x_124, x_129, x_131);
x_133 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
x_134 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
x_135 = l_Lean_addMacroScope(x_106, x_134, x_115);
lean_inc(x_103);
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_103);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_136, 3, x_128);
lean_inc(x_111);
lean_inc_ref(x_136);
lean_inc(x_103);
x_137 = l_Lean_Syntax_node2(x_103, x_124, x_136, x_111);
lean_inc(x_114);
lean_inc(x_103);
x_138 = l_Lean_Syntax_node3(x_103, x_114, x_132, x_108, x_137);
x_139 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_103);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_103);
lean_ctor_set(x_140, 1, x_139);
x_141 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_142 = l_Lean_Name_mkStr4(x_4, x_5, x_119, x_141);
lean_inc(x_103);
x_143 = l_Lean_Syntax_node2(x_103, x_114, x_129, x_136);
lean_inc(x_103);
x_144 = l_Lean_Syntax_node2(x_103, x_142, x_117, x_143);
x_145 = lean_unsigned_to_nat(10u);
x_146 = lean_mk_empty_array_with_capacity(x_145);
x_147 = lean_array_push(x_146, x_116);
x_148 = lean_array_push(x_147, x_105);
x_149 = lean_array_push(x_148, x_109);
x_150 = lean_array_push(x_149, x_113);
x_151 = lean_array_push(x_150, x_111);
x_152 = lean_array_push(x_151, x_120);
x_153 = lean_array_push(x_152, x_123);
x_154 = lean_array_push(x_153, x_138);
x_155 = lean_array_push(x_154, x_140);
x_156 = lean_array_push(x_155, x_144);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_103);
lean_ctor_set(x_157, 1, x_104);
lean_ctor_set(x_157, 2, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_107);
return x_158;
}
block_217:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_180 = l_Array_append___redArg(x_176, x_179);
lean_dec_ref(x_179);
lean_inc(x_169);
lean_inc(x_160);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_160);
lean_ctor_set(x_181, 1, x_169);
lean_ctor_set(x_181, 2, x_180);
x_182 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_183 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
x_184 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc(x_177);
lean_inc(x_167);
x_185 = l_Lean_addMacroScope(x_167, x_184, x_177);
x_186 = lean_box(0);
lean_inc(x_160);
x_187 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_187, 0, x_160);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_186);
lean_inc(x_160);
x_188 = l_Lean_Syntax_node2(x_160, x_165, x_170, x_163);
lean_inc(x_169);
lean_inc(x_160);
x_189 = l_Lean_Syntax_node1(x_160, x_169, x_188);
lean_inc(x_189);
lean_inc_ref(x_187);
lean_inc(x_160);
x_190 = l_Lean_Syntax_node2(x_160, x_182, x_187, x_189);
x_191 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
x_192 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
x_193 = l_Lean_addMacroScope(x_167, x_192, x_177);
lean_inc(x_160);
x_194 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_194, 0, x_160);
lean_ctor_set(x_194, 1, x_191);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_186);
lean_inc_ref(x_194);
lean_inc(x_160);
x_195 = l_Lean_Syntax_node2(x_160, x_182, x_194, x_189);
lean_inc(x_169);
lean_inc(x_160);
x_196 = l_Lean_Syntax_node3(x_160, x_169, x_190, x_166, x_195);
x_197 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_160);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_160);
lean_ctor_set(x_198, 1, x_197);
x_199 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_200 = l_Lean_Name_mkStr4(x_4, x_5, x_178, x_199);
lean_inc(x_160);
x_201 = l_Lean_Syntax_node2(x_160, x_169, x_187, x_194);
lean_inc(x_160);
x_202 = l_Lean_Syntax_node2(x_160, x_200, x_161, x_201);
x_203 = lean_unsigned_to_nat(10u);
x_204 = lean_mk_empty_array_with_capacity(x_203);
x_205 = lean_array_push(x_204, x_164);
x_206 = lean_array_push(x_205, x_174);
x_207 = lean_array_push(x_206, x_175);
x_208 = lean_array_push(x_207, x_173);
x_209 = lean_array_push(x_208, x_172);
x_210 = lean_array_push(x_209, x_171);
x_211 = lean_array_push(x_210, x_181);
x_212 = lean_array_push(x_211, x_196);
x_213 = lean_array_push(x_212, x_198);
x_214 = lean_array_push(x_213, x_202);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_160);
lean_ctor_set(x_215, 1, x_162);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_168);
return x_216;
}
block_275:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_238 = l_Array_append___redArg(x_222, x_237);
lean_dec_ref(x_237);
lean_inc(x_234);
lean_inc(x_226);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_226);
lean_ctor_set(x_239, 1, x_234);
lean_ctor_set(x_239, 2, x_238);
x_240 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_241 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11);
x_242 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12));
lean_inc(x_220);
lean_inc(x_225);
x_243 = l_Lean_addMacroScope(x_225, x_242, x_220);
x_244 = lean_box(0);
lean_inc(x_226);
x_245 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_245, 0, x_226);
lean_ctor_set(x_245, 1, x_241);
lean_ctor_set(x_245, 2, x_243);
lean_ctor_set(x_245, 3, x_244);
lean_inc(x_233);
lean_inc_ref(x_245);
lean_inc(x_226);
x_246 = l_Lean_Syntax_node2(x_226, x_240, x_245, x_233);
x_247 = lean_obj_once(&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14, &l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once, _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14);
x_248 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15));
x_249 = l_Lean_addMacroScope(x_225, x_248, x_220);
lean_inc(x_226);
x_250 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_250, 0, x_226);
lean_ctor_set(x_250, 1, x_247);
lean_ctor_set(x_250, 2, x_249);
lean_ctor_set(x_250, 3, x_244);
lean_inc(x_226);
x_251 = l_Lean_Syntax_node2(x_226, x_227, x_223, x_218);
lean_inc(x_234);
lean_inc(x_226);
x_252 = l_Lean_Syntax_node1(x_226, x_234, x_251);
lean_inc_ref(x_250);
lean_inc(x_226);
x_253 = l_Lean_Syntax_node2(x_226, x_240, x_250, x_252);
lean_inc(x_234);
lean_inc(x_226);
x_254 = l_Lean_Syntax_node3(x_226, x_234, x_246, x_219, x_253);
x_255 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_226);
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_226);
lean_ctor_set(x_256, 1, x_255);
x_257 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_258 = l_Lean_Name_mkStr4(x_4, x_5, x_235, x_257);
lean_inc(x_226);
x_259 = l_Lean_Syntax_node2(x_226, x_234, x_245, x_250);
lean_inc(x_226);
x_260 = l_Lean_Syntax_node2(x_226, x_258, x_236, x_259);
x_261 = lean_unsigned_to_nat(10u);
x_262 = lean_mk_empty_array_with_capacity(x_261);
x_263 = lean_array_push(x_262, x_232);
x_264 = lean_array_push(x_263, x_231);
x_265 = lean_array_push(x_264, x_230);
x_266 = lean_array_push(x_265, x_229);
x_267 = lean_array_push(x_266, x_233);
x_268 = lean_array_push(x_267, x_224);
x_269 = lean_array_push(x_268, x_239);
x_270 = lean_array_push(x_269, x_254);
x_271 = lean_array_push(x_270, x_256);
x_272 = lean_array_push(x_271, x_260);
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_226);
lean_ctor_set(x_273, 1, x_228);
lean_ctor_set(x_273, 2, x_272);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_221);
return x_274;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___closed__0));
x_5 = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17));
x_4 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMixfix), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2));
x_3 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Elab_Attributes(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Mixfix(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Attributes(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3()
;
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
res = initialize_Lean_Elab_Attributes(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Mixfix(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Mixfix(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Mixfix(builtin);
}
#ifdef __cplusplus
}
#endif
