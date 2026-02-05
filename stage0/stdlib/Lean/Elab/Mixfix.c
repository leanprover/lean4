// Lean compiler output
// Module: Lean.Elab.Mixfix
// Imports: public import Lean.Elab.Attributes
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
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(106, 194, 158, 37, 173, 85, 64, 87)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lhs"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_value;
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(246, 90, 165, 168, 14, 148, 243, 73)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_value;
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(149, 22, 109, 211, 70, 26, 115, 13)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mixfix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(1, 31, 80, 86, 44, 46, 155, 0)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__21 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__22 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__23 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__24 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__26 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__27 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__28 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__29 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__30 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__31 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__32 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__33 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__34 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__35 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__36 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__38 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__39 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__40 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "infixl"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__41 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value),LEAN_SCALAR_PTR_LITERAL(118, 176, 144, 146, 48, 231, 100, 173)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__42 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "infix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__43 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value),LEAN_SCALAR_PTR_LITERAL(8, 202, 116, 85, 196, 237, 101, 141)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__44 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "infixr"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__45 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value),LEAN_SCALAR_PTR_LITERAL(9, 7, 27, 92, 157, 7, 198, 225)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__46 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "prefix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__47 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value),LEAN_SCALAR_PTR_LITERAL(223, 255, 86, 177, 195, 168, 212, 163)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__48 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "postfix"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__49 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value),LEAN_SCALAR_PTR_LITERAL(97, 175, 134, 52, 144, 48, 141, 10)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__50 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__51 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__52 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__53 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value;
static const lean_string_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__54 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value;
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_expandMixfix___lam__0___closed__55 = (const lean_object*)&l_Lean_Elab_Command_expandMixfix___lam__0___closed__55_value;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Syntax_setArg(x_11, x_5, x_6);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_Syntax_setArg(x_13, x_5, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__11));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__14));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__37() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_271; uint8_t x_272; 
x_4 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0));
x_5 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1));
x_271 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__18));
lean_inc(x_1);
x_272 = l_Lean_Syntax_isOfKind(x_1, x_271);
if (x_272 == 0)
{
lean_object* x_273; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_273 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_705; lean_object* x_706; uint8_t x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; uint8_t x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1255; uint8_t x_1256; 
x_274 = lean_unsigned_to_nat(0u);
x_1255 = l_Lean_Syntax_getArg(x_1, x_274);
x_1256 = l_Lean_Syntax_isNone(x_1255);
if (x_1256 == 0)
{
lean_object* x_1257; uint8_t x_1258; 
x_1257 = lean_unsigned_to_nat(1u);
lean_inc(x_1255);
x_1258 = l_Lean_Syntax_matchesNull(x_1255, x_1257);
if (x_1258 == 0)
{
lean_object* x_1259; 
lean_dec(x_1255);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1259 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_1259;
}
else
{
lean_object* x_1260; lean_object* x_1261; uint8_t x_1262; 
x_1260 = l_Lean_Syntax_getArg(x_1255, x_274);
lean_dec(x_1255);
x_1261 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__55));
lean_inc(x_1260);
x_1262 = l_Lean_Syntax_isOfKind(x_1260, x_1261);
if (x_1262 == 0)
{
lean_object* x_1263; 
lean_dec(x_1260);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1263 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_1263;
}
else
{
lean_object* x_1264; 
x_1264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1264, 0, x_1260);
x_1238 = x_1264;
x_1239 = x_2;
x_1240 = x_3;
goto block_1254;
}
}
}
else
{
lean_object* x_1265; 
lean_dec(x_1255);
x_1265 = lean_box(0);
x_1238 = x_1265;
x_1239 = x_2;
x_1240 = x_3;
goto block_1254;
}
block_307:
{
lean_object* x_292; lean_object* x_293; 
lean_inc_ref(x_284);
x_292 = l_Array_append___redArg(x_284, x_291);
lean_dec_ref(x_291);
lean_inc(x_289);
lean_inc(x_278);
x_293 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_293, 0, x_278);
lean_ctor_set(x_293, 1, x_289);
lean_ctor_set(x_293, 2, x_292);
if (lean_obj_tag(x_279) == 1)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_294 = lean_ctor_get(x_279, 0);
lean_inc(x_294);
lean_dec_ref(x_279);
x_295 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
x_296 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_278);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_278);
lean_ctor_set(x_297, 1, x_296);
x_298 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_278);
x_299 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_299, 0, x_278);
lean_ctor_set(x_299, 1, x_298);
x_300 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_278);
x_301 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_301, 0, x_278);
lean_ctor_set(x_301, 1, x_300);
x_302 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_278);
x_303 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_303, 0, x_278);
lean_ctor_set(x_303, 1, x_302);
lean_inc(x_278);
x_304 = l_Lean_Syntax_node5(x_278, x_295, x_297, x_299, x_301, x_294, x_303);
x_305 = l_Array_mkArray1___redArg(x_304);
x_6 = x_275;
x_7 = x_276;
x_8 = x_277;
x_9 = x_293;
x_10 = x_278;
x_11 = x_280;
x_12 = x_281;
x_13 = x_282;
x_14 = x_283;
x_15 = x_284;
x_16 = x_285;
x_17 = x_286;
x_18 = x_287;
x_19 = x_288;
x_20 = x_289;
x_21 = x_290;
x_22 = x_305;
goto block_52;
}
else
{
lean_object* x_306; 
lean_dec(x_279);
x_306 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_6 = x_275;
x_7 = x_276;
x_8 = x_277;
x_9 = x_293;
x_10 = x_278;
x_11 = x_280;
x_12 = x_281;
x_13 = x_282;
x_14 = x_283;
x_15 = x_284;
x_16 = x_285;
x_17 = x_286;
x_18 = x_287;
x_19 = x_288;
x_20 = x_289;
x_21 = x_290;
x_22 = x_306;
goto block_52;
}
}
block_348:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_inc_ref(x_318);
x_326 = l_Array_append___redArg(x_318, x_325);
lean_dec_ref(x_325);
lean_inc(x_323);
lean_inc(x_311);
x_327 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_327, 0, x_311);
lean_ctor_set(x_327, 1, x_323);
lean_ctor_set(x_327, 2, x_326);
lean_inc_ref(x_318);
lean_inc(x_323);
lean_inc(x_311);
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_311);
lean_ctor_set(x_328, 1, x_323);
lean_ctor_set(x_328, 2, x_318);
lean_inc(x_311);
x_329 = l_Lean_Syntax_node1(x_311, x_314, x_328);
lean_inc(x_311);
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_311);
lean_ctor_set(x_330, 1, x_319);
x_331 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26));
lean_inc(x_311);
x_332 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_332, 0, x_311);
lean_ctor_set(x_332, 1, x_331);
lean_inc(x_311);
x_333 = l_Lean_Syntax_node2(x_311, x_308, x_332, x_322);
lean_inc(x_323);
lean_inc(x_311);
x_334 = l_Lean_Syntax_node1(x_311, x_323, x_333);
if (lean_obj_tag(x_320) == 1)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_335 = lean_ctor_get(x_320, 0);
lean_inc(x_335);
lean_dec_ref(x_320);
x_336 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
x_337 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_311);
x_338 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_338, 0, x_311);
lean_ctor_set(x_338, 1, x_337);
x_339 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc(x_311);
x_340 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_340, 0, x_311);
lean_ctor_set(x_340, 1, x_339);
x_341 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_311);
x_342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_342, 0, x_311);
lean_ctor_set(x_342, 1, x_341);
x_343 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_311);
x_344 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_344, 0, x_311);
lean_ctor_set(x_344, 1, x_343);
lean_inc(x_311);
x_345 = l_Lean_Syntax_node5(x_311, x_336, x_338, x_340, x_342, x_335, x_344);
x_346 = l_Array_mkArray1___redArg(x_345);
x_275 = x_309;
x_276 = x_310;
x_277 = x_334;
x_278 = x_311;
x_279 = x_312;
x_280 = x_313;
x_281 = x_329;
x_282 = x_315;
x_283 = x_316;
x_284 = x_318;
x_285 = x_317;
x_286 = x_321;
x_287 = x_330;
x_288 = x_327;
x_289 = x_323;
x_290 = x_324;
x_291 = x_346;
goto block_307;
}
else
{
lean_object* x_347; 
lean_dec(x_320);
x_347 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_275 = x_309;
x_276 = x_310;
x_277 = x_334;
x_278 = x_311;
x_279 = x_312;
x_280 = x_313;
x_281 = x_329;
x_282 = x_315;
x_283 = x_316;
x_284 = x_318;
x_285 = x_317;
x_286 = x_321;
x_287 = x_330;
x_288 = x_327;
x_289 = x_323;
x_290 = x_324;
x_291 = x_347;
goto block_307;
}
}
block_381:
{
lean_object* x_367; lean_object* x_368; 
lean_inc_ref(x_358);
x_367 = l_Array_append___redArg(x_358, x_366);
lean_dec_ref(x_366);
lean_inc(x_364);
lean_inc(x_351);
x_368 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_368, 0, x_351);
lean_ctor_set(x_368, 1, x_364);
lean_ctor_set(x_368, 2, x_367);
if (lean_obj_tag(x_355) == 1)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_369 = lean_ctor_get(x_355, 0);
lean_inc(x_369);
lean_dec_ref(x_355);
x_370 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_ref(x_363);
x_371 = l_Lean_Name_mkStr4(x_4, x_5, x_363, x_370);
x_372 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_351);
x_373 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_373, 0, x_351);
lean_ctor_set(x_373, 1, x_372);
lean_inc_ref(x_358);
x_374 = l_Array_append___redArg(x_358, x_369);
lean_dec(x_369);
lean_inc(x_364);
lean_inc(x_351);
x_375 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_375, 0, x_351);
lean_ctor_set(x_375, 1, x_364);
lean_ctor_set(x_375, 2, x_374);
x_376 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
lean_inc(x_351);
x_377 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_377, 0, x_351);
lean_ctor_set(x_377, 1, x_376);
lean_inc(x_351);
x_378 = l_Lean_Syntax_node3(x_351, x_371, x_373, x_375, x_377);
x_379 = l_Array_mkArray1___redArg(x_378);
x_308 = x_349;
x_309 = x_368;
x_310 = x_350;
x_311 = x_351;
x_312 = x_352;
x_313 = x_353;
x_314 = x_354;
x_315 = x_356;
x_316 = x_357;
x_317 = x_359;
x_318 = x_358;
x_319 = x_360;
x_320 = x_361;
x_321 = x_363;
x_322 = x_362;
x_323 = x_364;
x_324 = x_365;
x_325 = x_379;
goto block_348;
}
else
{
lean_object* x_380; 
lean_dec(x_355);
x_380 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_308 = x_349;
x_309 = x_368;
x_310 = x_350;
x_311 = x_351;
x_312 = x_352;
x_313 = x_353;
x_314 = x_354;
x_315 = x_356;
x_316 = x_357;
x_317 = x_359;
x_318 = x_358;
x_319 = x_360;
x_320 = x_361;
x_321 = x_363;
x_322 = x_362;
x_323 = x_364;
x_324 = x_365;
x_325 = x_380;
goto block_348;
}
}
block_408:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_391, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_391, 5);
lean_inc(x_395);
lean_dec_ref(x_391);
x_396 = lean_unsigned_to_nat(7u);
x_397 = l_Lean_Syntax_getArg(x_1, x_396);
x_398 = lean_unsigned_to_nat(9u);
x_399 = l_Lean_Syntax_getArg(x_1, x_398);
lean_dec(x_1);
x_400 = l_Lean_SourceInfo_fromRef(x_395, x_389);
lean_dec(x_395);
x_401 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_402 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34));
x_403 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36));
x_404 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
if (lean_obj_tag(x_385) == 1)
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_385, 0);
lean_inc(x_405);
lean_dec_ref(x_385);
x_406 = l_Array_mkArray1___redArg(x_405);
x_349 = x_383;
x_350 = x_402;
x_351 = x_400;
x_352 = x_390;
x_353 = x_392;
x_354 = x_382;
x_355 = x_384;
x_356 = x_397;
x_357 = x_399;
x_358 = x_404;
x_359 = x_394;
x_360 = x_401;
x_361 = x_386;
x_362 = x_388;
x_363 = x_387;
x_364 = x_403;
x_365 = x_393;
x_366 = x_406;
goto block_381;
}
else
{
lean_object* x_407; 
lean_dec(x_385);
x_407 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_349 = x_383;
x_350 = x_402;
x_351 = x_400;
x_352 = x_390;
x_353 = x_392;
x_354 = x_382;
x_355 = x_384;
x_356 = x_397;
x_357 = x_399;
x_358 = x_404;
x_359 = x_394;
x_360 = x_401;
x_361 = x_386;
x_362 = x_388;
x_363 = x_387;
x_364 = x_403;
x_365 = x_393;
x_366 = x_407;
goto block_381;
}
}
block_433:
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_421 = lean_unsigned_to_nat(6u);
x_422 = l_Lean_Syntax_getArg(x_1, x_421);
x_423 = l_Lean_Syntax_isNone(x_422);
if (x_423 == 0)
{
uint8_t x_424; 
lean_inc(x_422);
x_424 = l_Lean_Syntax_matchesNull(x_422, x_411);
if (x_424 == 0)
{
lean_object* x_425; 
lean_dec(x_422);
lean_dec_ref(x_419);
lean_dec(x_418);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_412);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_1);
x_425 = l_Lean_Macro_throwUnsupported___redArg(x_420);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_426 = l_Lean_Syntax_getArg(x_422, x_274);
lean_dec(x_422);
x_427 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_426);
x_428 = l_Lean_Syntax_isOfKind(x_426, x_427);
if (x_428 == 0)
{
lean_object* x_429; 
lean_dec(x_426);
lean_dec_ref(x_419);
lean_dec(x_418);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_412);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_1);
x_429 = l_Lean_Macro_throwUnsupported___redArg(x_420);
return x_429;
}
else
{
lean_object* x_430; lean_object* x_431; 
x_430 = l_Lean_Syntax_getArg(x_426, x_413);
lean_dec(x_426);
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_430);
x_382 = x_410;
x_383 = x_409;
x_384 = x_412;
x_385 = x_414;
x_386 = x_418;
x_387 = x_416;
x_388 = x_415;
x_389 = x_417;
x_390 = x_431;
x_391 = x_419;
x_392 = x_420;
goto block_408;
}
}
}
else
{
lean_object* x_432; 
lean_dec(x_422);
x_432 = lean_box(0);
x_382 = x_410;
x_383 = x_409;
x_384 = x_412;
x_385 = x_414;
x_386 = x_418;
x_387 = x_416;
x_388 = x_415;
x_389 = x_417;
x_390 = x_432;
x_391 = x_419;
x_392 = x_420;
goto block_408;
}
}
block_466:
{
lean_object* x_451; lean_object* x_452; 
lean_inc_ref(x_446);
x_451 = l_Array_append___redArg(x_446, x_450);
lean_dec_ref(x_450);
lean_inc(x_442);
lean_inc(x_445);
x_452 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_452, 0, x_445);
lean_ctor_set(x_452, 1, x_442);
lean_ctor_set(x_452, 2, x_451);
if (lean_obj_tag(x_434) == 1)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_453 = lean_ctor_get(x_434, 0);
lean_inc(x_453);
lean_dec_ref(x_434);
x_454 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
x_455 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_445);
x_456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_456, 0, x_445);
lean_ctor_set(x_456, 1, x_455);
x_457 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_445);
x_458 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_458, 0, x_445);
lean_ctor_set(x_458, 1, x_457);
x_459 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_445);
x_460 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_460, 0, x_445);
lean_ctor_set(x_460, 1, x_459);
x_461 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_445);
x_462 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_462, 0, x_445);
lean_ctor_set(x_462, 1, x_461);
lean_inc(x_445);
x_463 = l_Lean_Syntax_node5(x_445, x_454, x_456, x_458, x_460, x_453, x_462);
x_464 = l_Array_mkArray1___redArg(x_463);
x_53 = x_435;
x_54 = x_436;
x_55 = x_452;
x_56 = x_437;
x_57 = x_438;
x_58 = x_439;
x_59 = x_440;
x_60 = x_441;
x_61 = x_442;
x_62 = x_443;
x_63 = x_444;
x_64 = x_445;
x_65 = x_446;
x_66 = x_447;
x_67 = x_448;
x_68 = x_449;
x_69 = x_464;
goto block_99;
}
else
{
lean_object* x_465; 
lean_dec(x_434);
x_465 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_53 = x_435;
x_54 = x_436;
x_55 = x_452;
x_56 = x_437;
x_57 = x_438;
x_58 = x_439;
x_59 = x_440;
x_60 = x_441;
x_61 = x_442;
x_62 = x_443;
x_63 = x_444;
x_64 = x_445;
x_65 = x_446;
x_66 = x_447;
x_67 = x_448;
x_68 = x_449;
x_69 = x_465;
goto block_99;
}
}
block_507:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_inc_ref(x_480);
x_485 = l_Array_append___redArg(x_480, x_484);
lean_dec_ref(x_484);
lean_inc(x_475);
lean_inc(x_479);
x_486 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_486, 0, x_479);
lean_ctor_set(x_486, 1, x_475);
lean_ctor_set(x_486, 2, x_485);
lean_inc_ref(x_480);
lean_inc(x_475);
lean_inc(x_479);
x_487 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_487, 0, x_479);
lean_ctor_set(x_487, 1, x_475);
lean_ctor_set(x_487, 2, x_480);
lean_inc(x_479);
x_488 = l_Lean_Syntax_node1(x_479, x_476, x_487);
lean_inc(x_479);
x_489 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_489, 0, x_479);
lean_ctor_set(x_489, 1, x_471);
x_490 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26));
lean_inc(x_479);
x_491 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_491, 0, x_479);
lean_ctor_set(x_491, 1, x_490);
lean_inc(x_479);
x_492 = l_Lean_Syntax_node2(x_479, x_473, x_491, x_481);
lean_inc(x_475);
lean_inc(x_479);
x_493 = l_Lean_Syntax_node1(x_479, x_475, x_492);
if (lean_obj_tag(x_470) == 1)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_494 = lean_ctor_get(x_470, 0);
lean_inc(x_494);
lean_dec_ref(x_470);
x_495 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
x_496 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_479);
x_497 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_497, 0, x_479);
lean_ctor_set(x_497, 1, x_496);
x_498 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc(x_479);
x_499 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_499, 0, x_479);
lean_ctor_set(x_499, 1, x_498);
x_500 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_479);
x_501 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_501, 0, x_479);
lean_ctor_set(x_501, 1, x_500);
x_502 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_479);
x_503 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_503, 0, x_479);
lean_ctor_set(x_503, 1, x_502);
lean_inc(x_479);
x_504 = l_Lean_Syntax_node5(x_479, x_495, x_497, x_499, x_501, x_494, x_503);
x_505 = l_Array_mkArray1___redArg(x_504);
x_434 = x_467;
x_435 = x_468;
x_436 = x_469;
x_437 = x_493;
x_438 = x_486;
x_439 = x_472;
x_440 = x_489;
x_441 = x_474;
x_442 = x_475;
x_443 = x_478;
x_444 = x_477;
x_445 = x_479;
x_446 = x_480;
x_447 = x_488;
x_448 = x_482;
x_449 = x_483;
x_450 = x_505;
goto block_466;
}
else
{
lean_object* x_506; 
lean_dec(x_470);
x_506 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_434 = x_467;
x_435 = x_468;
x_436 = x_469;
x_437 = x_493;
x_438 = x_486;
x_439 = x_472;
x_440 = x_489;
x_441 = x_474;
x_442 = x_475;
x_443 = x_478;
x_444 = x_477;
x_445 = x_479;
x_446 = x_480;
x_447 = x_488;
x_448 = x_482;
x_449 = x_483;
x_450 = x_506;
goto block_466;
}
}
block_540:
{
lean_object* x_526; lean_object* x_527; 
lean_inc_ref(x_521);
x_526 = l_Array_append___redArg(x_521, x_525);
lean_dec_ref(x_525);
lean_inc(x_516);
lean_inc(x_520);
x_527 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_527, 0, x_520);
lean_ctor_set(x_527, 1, x_516);
lean_ctor_set(x_527, 2, x_526);
if (lean_obj_tag(x_519) == 1)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_528 = lean_ctor_get(x_519, 0);
lean_inc(x_528);
lean_dec_ref(x_519);
x_529 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_ref(x_523);
x_530 = l_Lean_Name_mkStr4(x_4, x_5, x_523, x_529);
x_531 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_520);
x_532 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_532, 0, x_520);
lean_ctor_set(x_532, 1, x_531);
lean_inc_ref(x_521);
x_533 = l_Array_append___redArg(x_521, x_528);
lean_dec(x_528);
lean_inc(x_516);
lean_inc(x_520);
x_534 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_534, 0, x_520);
lean_ctor_set(x_534, 1, x_516);
lean_ctor_set(x_534, 2, x_533);
x_535 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
lean_inc(x_520);
x_536 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_536, 0, x_520);
lean_ctor_set(x_536, 1, x_535);
lean_inc(x_520);
x_537 = l_Lean_Syntax_node3(x_520, x_530, x_532, x_534, x_536);
x_538 = l_Array_mkArray1___redArg(x_537);
x_467 = x_508;
x_468 = x_509;
x_469 = x_510;
x_470 = x_511;
x_471 = x_512;
x_472 = x_513;
x_473 = x_514;
x_474 = x_515;
x_475 = x_516;
x_476 = x_517;
x_477 = x_527;
x_478 = x_518;
x_479 = x_520;
x_480 = x_521;
x_481 = x_522;
x_482 = x_523;
x_483 = x_524;
x_484 = x_538;
goto block_507;
}
else
{
lean_object* x_539; 
lean_dec(x_519);
x_539 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_467 = x_508;
x_468 = x_509;
x_469 = x_510;
x_470 = x_511;
x_471 = x_512;
x_472 = x_513;
x_473 = x_514;
x_474 = x_515;
x_475 = x_516;
x_476 = x_517;
x_477 = x_527;
x_478 = x_518;
x_479 = x_520;
x_480 = x_521;
x_481 = x_522;
x_482 = x_523;
x_483 = x_524;
x_484 = x_539;
goto block_507;
}
}
block_567:
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
x_553 = lean_ctor_get(x_550, 2);
lean_inc(x_553);
x_554 = lean_ctor_get(x_550, 5);
lean_inc(x_554);
lean_dec_ref(x_550);
x_555 = lean_unsigned_to_nat(7u);
x_556 = l_Lean_Syntax_getArg(x_1, x_555);
x_557 = lean_unsigned_to_nat(9u);
x_558 = l_Lean_Syntax_getArg(x_1, x_557);
lean_dec(x_1);
x_559 = l_Lean_SourceInfo_fromRef(x_554, x_548);
lean_dec(x_554);
x_560 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_561 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34));
x_562 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36));
x_563 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
if (lean_obj_tag(x_545) == 1)
{
lean_object* x_564; lean_object* x_565; 
x_564 = lean_ctor_get(x_545, 0);
lean_inc(x_564);
lean_dec_ref(x_545);
x_565 = l_Array_mkArray1___redArg(x_564);
x_508 = x_549;
x_509 = x_561;
x_510 = x_552;
x_511 = x_543;
x_512 = x_560;
x_513 = x_556;
x_514 = x_546;
x_515 = x_558;
x_516 = x_562;
x_517 = x_541;
x_518 = x_553;
x_519 = x_542;
x_520 = x_559;
x_521 = x_563;
x_522 = x_544;
x_523 = x_547;
x_524 = x_551;
x_525 = x_565;
goto block_540;
}
else
{
lean_object* x_566; 
lean_dec(x_545);
x_566 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_508 = x_549;
x_509 = x_561;
x_510 = x_552;
x_511 = x_543;
x_512 = x_560;
x_513 = x_556;
x_514 = x_546;
x_515 = x_558;
x_516 = x_562;
x_517 = x_541;
x_518 = x_553;
x_519 = x_542;
x_520 = x_559;
x_521 = x_563;
x_522 = x_544;
x_523 = x_547;
x_524 = x_551;
x_525 = x_566;
goto block_540;
}
}
block_592:
{
lean_object* x_580; lean_object* x_581; uint8_t x_582; 
x_580 = lean_unsigned_to_nat(6u);
x_581 = l_Lean_Syntax_getArg(x_1, x_580);
x_582 = l_Lean_Syntax_isNone(x_581);
if (x_582 == 0)
{
uint8_t x_583; 
lean_inc(x_581);
x_583 = l_Lean_Syntax_matchesNull(x_581, x_569);
if (x_583 == 0)
{
lean_object* x_584; 
lean_dec(x_581);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_1);
x_584 = l_Lean_Macro_throwUnsupported___redArg(x_579);
return x_584;
}
else
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_585 = l_Lean_Syntax_getArg(x_581, x_274);
lean_dec(x_581);
x_586 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_585);
x_587 = l_Lean_Syntax_isOfKind(x_585, x_586);
if (x_587 == 0)
{
lean_object* x_588; 
lean_dec(x_585);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_1);
x_588 = l_Lean_Macro_throwUnsupported___redArg(x_579);
return x_588;
}
else
{
lean_object* x_589; lean_object* x_590; 
x_589 = l_Lean_Syntax_getArg(x_585, x_571);
lean_dec(x_585);
x_590 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_590, 0, x_589);
x_541 = x_568;
x_542 = x_570;
x_543 = x_577;
x_544 = x_572;
x_545 = x_573;
x_546 = x_574;
x_547 = x_575;
x_548 = x_576;
x_549 = x_590;
x_550 = x_578;
x_551 = x_579;
goto block_567;
}
}
}
else
{
lean_object* x_591; 
lean_dec(x_581);
x_591 = lean_box(0);
x_541 = x_568;
x_542 = x_570;
x_543 = x_577;
x_544 = x_572;
x_545 = x_573;
x_546 = x_574;
x_547 = x_575;
x_548 = x_576;
x_549 = x_591;
x_550 = x_578;
x_551 = x_579;
goto block_567;
}
}
block_628:
{
lean_object* x_613; lean_object* x_614; 
lean_inc_ref(x_598);
x_613 = l_Array_append___redArg(x_598, x_612);
lean_dec_ref(x_612);
lean_inc(x_595);
lean_inc(x_599);
x_614 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_614, 0, x_599);
lean_ctor_set(x_614, 1, x_595);
lean_ctor_set(x_614, 2, x_613);
if (lean_obj_tag(x_596) == 1)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_615 = lean_ctor_get(x_596, 0);
lean_inc(x_615);
lean_dec_ref(x_596);
x_616 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
x_617 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_599);
x_618 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_618, 0, x_599);
lean_ctor_set(x_618, 1, x_617);
x_619 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_599);
x_620 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_620, 0, x_599);
lean_ctor_set(x_620, 1, x_619);
x_621 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_599);
x_622 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_622, 0, x_599);
lean_ctor_set(x_622, 1, x_621);
x_623 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_599);
x_624 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_624, 0, x_599);
lean_ctor_set(x_624, 1, x_623);
lean_inc(x_599);
x_625 = l_Lean_Syntax_node5(x_599, x_616, x_618, x_620, x_622, x_615, x_624);
x_626 = l_Array_mkArray1___redArg(x_625);
x_100 = x_593;
x_101 = x_594;
x_102 = x_595;
x_103 = x_597;
x_104 = x_598;
x_105 = x_599;
x_106 = x_600;
x_107 = x_601;
x_108 = x_602;
x_109 = x_603;
x_110 = x_604;
x_111 = x_614;
x_112 = x_607;
x_113 = x_608;
x_114 = x_606;
x_115 = x_605;
x_116 = x_610;
x_117 = x_609;
x_118 = x_611;
x_119 = x_626;
goto block_156;
}
else
{
lean_object* x_627; 
lean_dec(x_596);
x_627 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_100 = x_593;
x_101 = x_594;
x_102 = x_595;
x_103 = x_597;
x_104 = x_598;
x_105 = x_599;
x_106 = x_600;
x_107 = x_601;
x_108 = x_602;
x_109 = x_603;
x_110 = x_604;
x_111 = x_614;
x_112 = x_607;
x_113 = x_608;
x_114 = x_606;
x_115 = x_605;
x_116 = x_610;
x_117 = x_609;
x_118 = x_611;
x_119 = x_627;
goto block_156;
}
}
block_670:
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_inc_ref(x_633);
x_648 = l_Array_append___redArg(x_633, x_647);
lean_dec_ref(x_647);
lean_inc(x_630);
lean_inc(x_635);
x_649 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_649, 0, x_635);
lean_ctor_set(x_649, 1, x_630);
lean_ctor_set(x_649, 2, x_648);
lean_inc_ref(x_633);
lean_inc(x_630);
lean_inc(x_635);
x_650 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_650, 0, x_635);
lean_ctor_set(x_650, 1, x_630);
lean_ctor_set(x_650, 2, x_633);
lean_inc(x_635);
x_651 = l_Lean_Syntax_node1(x_635, x_640, x_650);
lean_inc(x_635);
x_652 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_652, 0, x_635);
lean_ctor_set(x_652, 1, x_638);
x_653 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26));
lean_inc(x_635);
x_654 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_654, 0, x_635);
lean_ctor_set(x_654, 1, x_653);
lean_inc_ref(x_654);
lean_inc(x_641);
lean_inc(x_635);
x_655 = l_Lean_Syntax_node2(x_635, x_641, x_654, x_642);
lean_inc(x_630);
lean_inc(x_635);
x_656 = l_Lean_Syntax_node1(x_635, x_630, x_655);
if (lean_obj_tag(x_634) == 1)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_657 = lean_ctor_get(x_634, 0);
lean_inc(x_657);
lean_dec_ref(x_634);
x_658 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
x_659 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_635);
x_660 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_660, 0, x_635);
lean_ctor_set(x_660, 1, x_659);
x_661 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc(x_635);
x_662 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_662, 0, x_635);
lean_ctor_set(x_662, 1, x_661);
x_663 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_635);
x_664 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_664, 0, x_635);
lean_ctor_set(x_664, 1, x_663);
x_665 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_635);
x_666 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_666, 0, x_635);
lean_ctor_set(x_666, 1, x_665);
lean_inc(x_635);
x_667 = l_Lean_Syntax_node5(x_635, x_658, x_660, x_662, x_664, x_657, x_666);
x_668 = l_Array_mkArray1___redArg(x_667);
x_593 = x_629;
x_594 = x_651;
x_595 = x_630;
x_596 = x_631;
x_597 = x_632;
x_598 = x_633;
x_599 = x_635;
x_600 = x_636;
x_601 = x_649;
x_602 = x_637;
x_603 = x_639;
x_604 = x_641;
x_605 = x_644;
x_606 = x_656;
x_607 = x_643;
x_608 = x_654;
x_609 = x_646;
x_610 = x_645;
x_611 = x_652;
x_612 = x_668;
goto block_628;
}
else
{
lean_object* x_669; 
lean_dec(x_634);
x_669 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_593 = x_629;
x_594 = x_651;
x_595 = x_630;
x_596 = x_631;
x_597 = x_632;
x_598 = x_633;
x_599 = x_635;
x_600 = x_636;
x_601 = x_649;
x_602 = x_637;
x_603 = x_639;
x_604 = x_641;
x_605 = x_644;
x_606 = x_656;
x_607 = x_643;
x_608 = x_654;
x_609 = x_646;
x_610 = x_645;
x_611 = x_652;
x_612 = x_669;
goto block_628;
}
}
block_704:
{
lean_object* x_690; lean_object* x_691; 
lean_inc_ref(x_675);
x_690 = l_Array_append___redArg(x_675, x_689);
lean_dec_ref(x_689);
lean_inc(x_672);
lean_inc(x_677);
x_691 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_691, 0, x_677);
lean_ctor_set(x_691, 1, x_672);
lean_ctor_set(x_691, 2, x_690);
if (lean_obj_tag(x_683) == 1)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_692 = lean_ctor_get(x_683, 0);
lean_inc(x_692);
lean_dec_ref(x_683);
x_693 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_ref(x_685);
x_694 = l_Lean_Name_mkStr4(x_4, x_5, x_685, x_693);
x_695 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_677);
x_696 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_696, 0, x_677);
lean_ctor_set(x_696, 1, x_695);
lean_inc_ref(x_675);
x_697 = l_Array_append___redArg(x_675, x_692);
lean_dec(x_692);
lean_inc(x_672);
lean_inc(x_677);
x_698 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_698, 0, x_677);
lean_ctor_set(x_698, 1, x_672);
lean_ctor_set(x_698, 2, x_697);
x_699 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
lean_inc(x_677);
x_700 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_700, 0, x_677);
lean_ctor_set(x_700, 1, x_699);
lean_inc(x_677);
x_701 = l_Lean_Syntax_node3(x_677, x_694, x_696, x_698, x_700);
x_702 = l_Array_mkArray1___redArg(x_701);
x_629 = x_671;
x_630 = x_672;
x_631 = x_673;
x_632 = x_674;
x_633 = x_675;
x_634 = x_676;
x_635 = x_677;
x_636 = x_678;
x_637 = x_691;
x_638 = x_679;
x_639 = x_680;
x_640 = x_681;
x_641 = x_682;
x_642 = x_684;
x_643 = x_686;
x_644 = x_685;
x_645 = x_688;
x_646 = x_687;
x_647 = x_702;
goto block_670;
}
else
{
lean_object* x_703; 
lean_dec(x_683);
x_703 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_629 = x_671;
x_630 = x_672;
x_631 = x_673;
x_632 = x_674;
x_633 = x_675;
x_634 = x_676;
x_635 = x_677;
x_636 = x_678;
x_637 = x_691;
x_638 = x_679;
x_639 = x_680;
x_640 = x_681;
x_641 = x_682;
x_642 = x_684;
x_643 = x_686;
x_644 = x_685;
x_645 = x_688;
x_646 = x_687;
x_647 = x_703;
goto block_670;
}
}
block_743:
{
lean_object* x_717; 
lean_inc_ref(x_715);
lean_inc(x_710);
x_717 = l_Lean_evalPrec(x_710, x_715, x_716);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec_ref(x_717);
x_720 = lean_ctor_get(x_715, 1);
lean_inc(x_720);
x_721 = lean_ctor_get(x_715, 2);
lean_inc(x_721);
x_722 = lean_ctor_get(x_715, 5);
lean_inc(x_722);
lean_dec_ref(x_715);
x_723 = lean_unsigned_to_nat(7u);
x_724 = l_Lean_Syntax_getArg(x_1, x_723);
x_725 = lean_unsigned_to_nat(9u);
x_726 = l_Lean_Syntax_getArg(x_1, x_725);
lean_dec(x_1);
x_727 = lean_nat_add(x_718, x_708);
lean_dec(x_718);
x_728 = l_Nat_reprFast(x_727);
x_729 = lean_box(2);
x_730 = l_Lean_Syntax_mkNumLit(x_728, x_729);
x_731 = l_Lean_SourceInfo_fromRef(x_722, x_707);
lean_dec(x_722);
x_732 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_733 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34));
x_734 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36));
x_735 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
if (lean_obj_tag(x_712) == 1)
{
lean_object* x_736; lean_object* x_737; 
x_736 = lean_ctor_get(x_712, 0);
lean_inc(x_736);
lean_dec_ref(x_712);
x_737 = l_Array_mkArray1___redArg(x_736);
x_671 = x_719;
x_672 = x_734;
x_673 = x_714;
x_674 = x_733;
x_675 = x_735;
x_676 = x_711;
x_677 = x_731;
x_678 = x_724;
x_679 = x_732;
x_680 = x_726;
x_681 = x_706;
x_682 = x_705;
x_683 = x_709;
x_684 = x_710;
x_685 = x_713;
x_686 = x_721;
x_687 = x_730;
x_688 = x_720;
x_689 = x_737;
goto block_704;
}
else
{
lean_object* x_738; 
lean_dec(x_712);
x_738 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_671 = x_719;
x_672 = x_734;
x_673 = x_714;
x_674 = x_733;
x_675 = x_735;
x_676 = x_711;
x_677 = x_731;
x_678 = x_724;
x_679 = x_732;
x_680 = x_726;
x_681 = x_706;
x_682 = x_705;
x_683 = x_709;
x_684 = x_710;
x_685 = x_713;
x_686 = x_721;
x_687 = x_730;
x_688 = x_720;
x_689 = x_738;
goto block_704;
}
}
else
{
uint8_t x_739; 
lean_dec_ref(x_715);
lean_dec(x_714);
lean_dec_ref(x_713);
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_706);
lean_dec(x_705);
lean_dec(x_1);
x_739 = !lean_is_exclusive(x_717);
if (x_739 == 0)
{
return x_717;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_717, 0);
x_741 = lean_ctor_get(x_717, 1);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_717);
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set(x_742, 1, x_741);
return x_742;
}
}
}
block_768:
{
lean_object* x_756; lean_object* x_757; uint8_t x_758; 
x_756 = lean_unsigned_to_nat(6u);
x_757 = l_Lean_Syntax_getArg(x_1, x_756);
x_758 = l_Lean_Syntax_isNone(x_757);
if (x_758 == 0)
{
uint8_t x_759; 
lean_inc(x_757);
x_759 = l_Lean_Syntax_matchesNull(x_757, x_746);
if (x_759 == 0)
{
lean_object* x_760; 
lean_dec(x_757);
lean_dec_ref(x_754);
lean_dec(x_753);
lean_dec_ref(x_752);
lean_dec(x_751);
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_1);
x_760 = l_Lean_Macro_throwUnsupported___redArg(x_755);
return x_760;
}
else
{
lean_object* x_761; lean_object* x_762; uint8_t x_763; 
x_761 = l_Lean_Syntax_getArg(x_757, x_274);
lean_dec(x_757);
x_762 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_761);
x_763 = l_Lean_Syntax_isOfKind(x_761, x_762);
if (x_763 == 0)
{
lean_object* x_764; 
lean_dec(x_761);
lean_dec_ref(x_754);
lean_dec(x_753);
lean_dec_ref(x_752);
lean_dec(x_751);
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_1);
x_764 = l_Lean_Macro_throwUnsupported___redArg(x_755);
return x_764;
}
else
{
lean_object* x_765; lean_object* x_766; 
x_765 = l_Lean_Syntax_getArg(x_761, x_750);
lean_dec(x_761);
x_766 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_766, 0, x_765);
x_705 = x_745;
x_706 = x_744;
x_707 = x_747;
x_708 = x_746;
x_709 = x_749;
x_710 = x_748;
x_711 = x_753;
x_712 = x_751;
x_713 = x_752;
x_714 = x_766;
x_715 = x_754;
x_716 = x_755;
goto block_743;
}
}
}
else
{
lean_object* x_767; 
lean_dec(x_757);
x_767 = lean_box(0);
x_705 = x_745;
x_706 = x_744;
x_707 = x_747;
x_708 = x_746;
x_709 = x_749;
x_710 = x_748;
x_711 = x_753;
x_712 = x_751;
x_713 = x_752;
x_714 = x_767;
x_715 = x_754;
x_716 = x_755;
goto block_743;
}
}
block_804:
{
lean_object* x_789; lean_object* x_790; 
lean_inc_ref(x_773);
x_789 = l_Array_append___redArg(x_773, x_788);
lean_dec_ref(x_788);
lean_inc(x_782);
lean_inc(x_772);
x_790 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_790, 0, x_772);
lean_ctor_set(x_790, 1, x_782);
lean_ctor_set(x_790, 2, x_789);
if (lean_obj_tag(x_771) == 1)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_791 = lean_ctor_get(x_771, 0);
lean_inc(x_791);
lean_dec_ref(x_771);
x_792 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
x_793 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_772);
x_794 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_794, 0, x_772);
lean_ctor_set(x_794, 1, x_793);
x_795 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_772);
x_796 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_796, 0, x_772);
lean_ctor_set(x_796, 1, x_795);
x_797 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_772);
x_798 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_798, 0, x_772);
lean_ctor_set(x_798, 1, x_797);
x_799 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_772);
x_800 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_800, 0, x_772);
lean_ctor_set(x_800, 1, x_799);
lean_inc(x_772);
x_801 = l_Lean_Syntax_node5(x_772, x_792, x_794, x_796, x_798, x_791, x_800);
x_802 = l_Array_mkArray1___redArg(x_801);
x_157 = x_769;
x_158 = x_770;
x_159 = x_772;
x_160 = x_773;
x_161 = x_774;
x_162 = x_775;
x_163 = x_776;
x_164 = x_777;
x_165 = x_778;
x_166 = x_790;
x_167 = x_779;
x_168 = x_780;
x_169 = x_781;
x_170 = x_782;
x_171 = x_783;
x_172 = x_785;
x_173 = x_784;
x_174 = x_786;
x_175 = x_787;
x_176 = x_802;
goto block_213;
}
else
{
lean_object* x_803; 
lean_dec(x_771);
x_803 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_157 = x_769;
x_158 = x_770;
x_159 = x_772;
x_160 = x_773;
x_161 = x_774;
x_162 = x_775;
x_163 = x_776;
x_164 = x_777;
x_165 = x_778;
x_166 = x_790;
x_167 = x_779;
x_168 = x_780;
x_169 = x_781;
x_170 = x_782;
x_171 = x_783;
x_172 = x_785;
x_173 = x_784;
x_174 = x_786;
x_175 = x_787;
x_176 = x_803;
goto block_213;
}
}
block_846:
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_inc_ref(x_809);
x_824 = l_Array_append___redArg(x_809, x_823);
lean_dec_ref(x_823);
lean_inc(x_816);
lean_inc(x_807);
x_825 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_825, 0, x_807);
lean_ctor_set(x_825, 1, x_816);
lean_ctor_set(x_825, 2, x_824);
lean_inc_ref(x_809);
lean_inc(x_816);
lean_inc(x_807);
x_826 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_826, 0, x_807);
lean_ctor_set(x_826, 1, x_816);
lean_ctor_set(x_826, 2, x_809);
lean_inc(x_807);
x_827 = l_Lean_Syntax_node1(x_807, x_815, x_826);
lean_inc(x_807);
x_828 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_828, 0, x_807);
lean_ctor_set(x_828, 1, x_817);
x_829 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26));
lean_inc(x_807);
x_830 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_830, 0, x_807);
lean_ctor_set(x_830, 1, x_829);
lean_inc_ref(x_830);
lean_inc(x_812);
lean_inc(x_807);
x_831 = l_Lean_Syntax_node2(x_807, x_812, x_830, x_810);
lean_inc(x_816);
lean_inc(x_807);
x_832 = l_Lean_Syntax_node1(x_807, x_816, x_831);
if (lean_obj_tag(x_805) == 1)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_833 = lean_ctor_get(x_805, 0);
lean_inc(x_833);
lean_dec_ref(x_805);
x_834 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
x_835 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_807);
x_836 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_836, 0, x_807);
lean_ctor_set(x_836, 1, x_835);
x_837 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc(x_807);
x_838 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_838, 0, x_807);
lean_ctor_set(x_838, 1, x_837);
x_839 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_807);
x_840 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_840, 0, x_807);
lean_ctor_set(x_840, 1, x_839);
x_841 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_807);
x_842 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_842, 0, x_807);
lean_ctor_set(x_842, 1, x_841);
lean_inc(x_807);
x_843 = l_Lean_Syntax_node5(x_807, x_834, x_836, x_838, x_840, x_833, x_842);
x_844 = l_Array_mkArray1___redArg(x_843);
x_769 = x_832;
x_770 = x_806;
x_771 = x_808;
x_772 = x_807;
x_773 = x_809;
x_774 = x_827;
x_775 = x_811;
x_776 = x_825;
x_777 = x_828;
x_778 = x_830;
x_779 = x_812;
x_780 = x_813;
x_781 = x_814;
x_782 = x_816;
x_783 = x_818;
x_784 = x_820;
x_785 = x_819;
x_786 = x_821;
x_787 = x_822;
x_788 = x_844;
goto block_804;
}
else
{
lean_object* x_845; 
lean_dec(x_805);
x_845 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_769 = x_832;
x_770 = x_806;
x_771 = x_808;
x_772 = x_807;
x_773 = x_809;
x_774 = x_827;
x_775 = x_811;
x_776 = x_825;
x_777 = x_828;
x_778 = x_830;
x_779 = x_812;
x_780 = x_813;
x_781 = x_814;
x_782 = x_816;
x_783 = x_818;
x_784 = x_820;
x_785 = x_819;
x_786 = x_821;
x_787 = x_822;
x_788 = x_845;
goto block_804;
}
}
block_880:
{
lean_object* x_866; lean_object* x_867; 
lean_inc_ref(x_851);
x_866 = l_Array_append___redArg(x_851, x_865);
lean_dec_ref(x_865);
lean_inc(x_857);
lean_inc(x_849);
x_867 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_867, 0, x_849);
lean_ctor_set(x_867, 1, x_857);
lean_ctor_set(x_867, 2, x_866);
if (lean_obj_tag(x_859) == 1)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_868 = lean_ctor_get(x_859, 0);
lean_inc(x_868);
lean_dec_ref(x_859);
x_869 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_ref(x_864);
x_870 = l_Lean_Name_mkStr4(x_4, x_5, x_864, x_869);
x_871 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_849);
x_872 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_872, 0, x_849);
lean_ctor_set(x_872, 1, x_871);
lean_inc_ref(x_851);
x_873 = l_Array_append___redArg(x_851, x_868);
lean_dec(x_868);
lean_inc(x_857);
lean_inc(x_849);
x_874 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_874, 0, x_849);
lean_ctor_set(x_874, 1, x_857);
lean_ctor_set(x_874, 2, x_873);
x_875 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
lean_inc(x_849);
x_876 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_876, 0, x_849);
lean_ctor_set(x_876, 1, x_875);
lean_inc(x_849);
x_877 = l_Lean_Syntax_node3(x_849, x_870, x_872, x_874, x_876);
x_878 = l_Array_mkArray1___redArg(x_877);
x_805 = x_847;
x_806 = x_848;
x_807 = x_849;
x_808 = x_850;
x_809 = x_851;
x_810 = x_852;
x_811 = x_867;
x_812 = x_853;
x_813 = x_854;
x_814 = x_855;
x_815 = x_856;
x_816 = x_857;
x_817 = x_858;
x_818 = x_860;
x_819 = x_862;
x_820 = x_861;
x_821 = x_863;
x_822 = x_864;
x_823 = x_878;
goto block_846;
}
else
{
lean_object* x_879; 
lean_dec(x_859);
x_879 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_805 = x_847;
x_806 = x_848;
x_807 = x_849;
x_808 = x_850;
x_809 = x_851;
x_810 = x_852;
x_811 = x_867;
x_812 = x_853;
x_813 = x_854;
x_814 = x_855;
x_815 = x_856;
x_816 = x_857;
x_817 = x_858;
x_818 = x_860;
x_819 = x_862;
x_820 = x_861;
x_821 = x_863;
x_822 = x_864;
x_823 = x_879;
goto block_846;
}
}
block_919:
{
lean_object* x_893; 
lean_inc_ref(x_891);
lean_inc(x_886);
x_893 = l_Lean_evalPrec(x_886, x_891, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec_ref(x_893);
x_896 = lean_ctor_get(x_891, 1);
lean_inc(x_896);
x_897 = lean_ctor_get(x_891, 2);
lean_inc(x_897);
x_898 = lean_ctor_get(x_891, 5);
lean_inc(x_898);
lean_dec_ref(x_891);
x_899 = lean_unsigned_to_nat(7u);
x_900 = l_Lean_Syntax_getArg(x_1, x_899);
x_901 = lean_unsigned_to_nat(9u);
x_902 = l_Lean_Syntax_getArg(x_1, x_901);
lean_dec(x_1);
x_903 = lean_nat_add(x_894, x_883);
lean_dec(x_894);
x_904 = l_Nat_reprFast(x_903);
x_905 = lean_box(2);
x_906 = l_Lean_Syntax_mkNumLit(x_904, x_905);
x_907 = l_Lean_SourceInfo_fromRef(x_898, x_885);
lean_dec(x_898);
x_908 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_909 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34));
x_910 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36));
x_911 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
if (lean_obj_tag(x_887) == 1)
{
lean_object* x_912; lean_object* x_913; 
x_912 = lean_ctor_get(x_887, 0);
lean_inc(x_912);
lean_dec_ref(x_887);
x_913 = l_Array_mkArray1___redArg(x_912);
x_847 = x_882;
x_848 = x_906;
x_849 = x_907;
x_850 = x_890;
x_851 = x_911;
x_852 = x_886;
x_853 = x_889;
x_854 = x_896;
x_855 = x_902;
x_856 = x_881;
x_857 = x_910;
x_858 = x_908;
x_859 = x_884;
x_860 = x_909;
x_861 = x_900;
x_862 = x_895;
x_863 = x_897;
x_864 = x_888;
x_865 = x_913;
goto block_880;
}
else
{
lean_object* x_914; 
lean_dec(x_887);
x_914 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_847 = x_882;
x_848 = x_906;
x_849 = x_907;
x_850 = x_890;
x_851 = x_911;
x_852 = x_886;
x_853 = x_889;
x_854 = x_896;
x_855 = x_902;
x_856 = x_881;
x_857 = x_910;
x_858 = x_908;
x_859 = x_884;
x_860 = x_909;
x_861 = x_900;
x_862 = x_895;
x_863 = x_897;
x_864 = x_888;
x_865 = x_914;
goto block_880;
}
}
else
{
uint8_t x_915; 
lean_dec_ref(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec_ref(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_884);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_1);
x_915 = !lean_is_exclusive(x_893);
if (x_915 == 0)
{
return x_893;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_893, 0);
x_917 = lean_ctor_get(x_893, 1);
lean_inc(x_917);
lean_inc(x_916);
lean_dec(x_893);
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
return x_918;
}
}
}
block_944:
{
lean_object* x_932; lean_object* x_933; uint8_t x_934; 
x_932 = lean_unsigned_to_nat(6u);
x_933 = l_Lean_Syntax_getArg(x_1, x_932);
x_934 = l_Lean_Syntax_isNone(x_933);
if (x_934 == 0)
{
uint8_t x_935; 
lean_inc(x_933);
x_935 = l_Lean_Syntax_matchesNull(x_933, x_921);
if (x_935 == 0)
{
lean_object* x_936; 
lean_dec(x_933);
lean_dec_ref(x_930);
lean_dec(x_929);
lean_dec(x_928);
lean_dec_ref(x_927);
lean_dec(x_926);
lean_dec(x_925);
lean_dec(x_922);
lean_dec(x_920);
lean_dec(x_1);
x_936 = l_Lean_Macro_throwUnsupported___redArg(x_931);
return x_936;
}
else
{
lean_object* x_937; lean_object* x_938; uint8_t x_939; 
x_937 = l_Lean_Syntax_getArg(x_933, x_274);
lean_dec(x_933);
x_938 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_937);
x_939 = l_Lean_Syntax_isOfKind(x_937, x_938);
if (x_939 == 0)
{
lean_object* x_940; 
lean_dec(x_937);
lean_dec_ref(x_930);
lean_dec(x_929);
lean_dec(x_928);
lean_dec_ref(x_927);
lean_dec(x_926);
lean_dec(x_925);
lean_dec(x_922);
lean_dec(x_920);
lean_dec(x_1);
x_940 = l_Lean_Macro_throwUnsupported___redArg(x_931);
return x_940;
}
else
{
lean_object* x_941; lean_object* x_942; 
x_941 = l_Lean_Syntax_getArg(x_937, x_923);
lean_dec(x_937);
x_942 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_942, 0, x_941);
x_881 = x_920;
x_882 = x_929;
x_883 = x_921;
x_884 = x_922;
x_885 = x_924;
x_886 = x_925;
x_887 = x_926;
x_888 = x_927;
x_889 = x_928;
x_890 = x_942;
x_891 = x_930;
x_892 = x_931;
goto block_919;
}
}
}
else
{
lean_object* x_943; 
lean_dec(x_933);
x_943 = lean_box(0);
x_881 = x_920;
x_882 = x_929;
x_883 = x_921;
x_884 = x_922;
x_885 = x_924;
x_886 = x_925;
x_887 = x_926;
x_888 = x_927;
x_889 = x_928;
x_890 = x_943;
x_891 = x_930;
x_892 = x_931;
goto block_919;
}
}
block_980:
{
lean_object* x_965; lean_object* x_966; 
lean_inc_ref(x_951);
x_965 = l_Array_append___redArg(x_951, x_964);
lean_dec_ref(x_964);
lean_inc(x_956);
lean_inc(x_963);
x_966 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_956);
lean_ctor_set(x_966, 2, x_965);
if (lean_obj_tag(x_947) == 1)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_967 = lean_ctor_get(x_947, 0);
lean_inc(x_967);
lean_dec_ref(x_947);
x_968 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
x_969 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_963);
x_970 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_970, 0, x_963);
lean_ctor_set(x_970, 1, x_969);
x_971 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22));
lean_inc(x_963);
x_972 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_972, 0, x_963);
lean_ctor_set(x_972, 1, x_971);
x_973 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_963);
x_974 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_974, 0, x_963);
lean_ctor_set(x_974, 1, x_973);
x_975 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_963);
x_976 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_976, 0, x_963);
lean_ctor_set(x_976, 1, x_975);
lean_inc(x_963);
x_977 = l_Lean_Syntax_node5(x_963, x_968, x_970, x_972, x_974, x_967, x_976);
x_978 = l_Array_mkArray1___redArg(x_977);
x_214 = x_945;
x_215 = x_946;
x_216 = x_948;
x_217 = x_949;
x_218 = x_950;
x_219 = x_952;
x_220 = x_953;
x_221 = x_951;
x_222 = x_954;
x_223 = x_955;
x_224 = x_956;
x_225 = x_957;
x_226 = x_958;
x_227 = x_959;
x_228 = x_966;
x_229 = x_960;
x_230 = x_961;
x_231 = x_963;
x_232 = x_962;
x_233 = x_978;
goto block_270;
}
else
{
lean_object* x_979; 
lean_dec(x_947);
x_979 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_214 = x_945;
x_215 = x_946;
x_216 = x_948;
x_217 = x_949;
x_218 = x_950;
x_219 = x_952;
x_220 = x_953;
x_221 = x_951;
x_222 = x_954;
x_223 = x_955;
x_224 = x_956;
x_225 = x_957;
x_226 = x_958;
x_227 = x_959;
x_228 = x_966;
x_229 = x_960;
x_230 = x_961;
x_231 = x_963;
x_232 = x_962;
x_233 = x_979;
goto block_270;
}
}
block_1022:
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
lean_inc_ref(x_985);
x_1000 = l_Array_append___redArg(x_985, x_999);
lean_dec_ref(x_999);
lean_inc(x_987);
lean_inc(x_998);
x_1001 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1001, 0, x_998);
lean_ctor_set(x_1001, 1, x_987);
lean_ctor_set(x_1001, 2, x_1000);
lean_inc_ref(x_985);
lean_inc(x_987);
lean_inc(x_998);
x_1002 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1002, 0, x_998);
lean_ctor_set(x_1002, 1, x_987);
lean_ctor_set(x_1002, 2, x_985);
lean_inc(x_998);
x_1003 = l_Lean_Syntax_node1(x_998, x_992, x_1002);
lean_inc(x_998);
x_1004 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1004, 0, x_998);
lean_ctor_set(x_1004, 1, x_995);
x_1005 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26));
lean_inc(x_998);
x_1006 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1006, 0, x_998);
lean_ctor_set(x_1006, 1, x_1005);
lean_inc_ref(x_1006);
lean_inc(x_990);
lean_inc(x_998);
x_1007 = l_Lean_Syntax_node2(x_998, x_990, x_1006, x_994);
lean_inc(x_987);
lean_inc(x_998);
x_1008 = l_Lean_Syntax_node1(x_998, x_987, x_1007);
if (lean_obj_tag(x_989) == 1)
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1009 = lean_ctor_get(x_989, 0);
lean_inc(x_1009);
lean_dec_ref(x_989);
x_1010 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
x_1011 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21));
lean_inc(x_998);
x_1012 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1012, 0, x_998);
lean_ctor_set(x_1012, 1, x_1011);
x_1013 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29));
lean_inc(x_998);
x_1014 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1014, 0, x_998);
lean_ctor_set(x_1014, 1, x_1013);
x_1015 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23));
lean_inc(x_998);
x_1016 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1016, 0, x_998);
lean_ctor_set(x_1016, 1, x_1015);
x_1017 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24));
lean_inc(x_998);
x_1018 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1018, 0, x_998);
lean_ctor_set(x_1018, 1, x_1017);
lean_inc(x_998);
x_1019 = l_Lean_Syntax_node5(x_998, x_1010, x_1012, x_1014, x_1016, x_1009, x_1018);
x_1020 = l_Array_mkArray1___redArg(x_1019);
x_945 = x_1004;
x_946 = x_981;
x_947 = x_982;
x_948 = x_1001;
x_949 = x_983;
x_950 = x_984;
x_951 = x_985;
x_952 = x_986;
x_953 = x_1003;
x_954 = x_1008;
x_955 = x_1006;
x_956 = x_987;
x_957 = x_988;
x_958 = x_990;
x_959 = x_991;
x_960 = x_993;
x_961 = x_996;
x_962 = x_997;
x_963 = x_998;
x_964 = x_1020;
goto block_980;
}
else
{
lean_object* x_1021; 
lean_dec(x_989);
x_1021 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_945 = x_1004;
x_946 = x_981;
x_947 = x_982;
x_948 = x_1001;
x_949 = x_983;
x_950 = x_984;
x_951 = x_985;
x_952 = x_986;
x_953 = x_1003;
x_954 = x_1008;
x_955 = x_1006;
x_956 = x_987;
x_957 = x_988;
x_958 = x_990;
x_959 = x_991;
x_960 = x_993;
x_961 = x_996;
x_962 = x_997;
x_963 = x_998;
x_964 = x_1021;
goto block_980;
}
}
block_1056:
{
lean_object* x_1042; lean_object* x_1043; 
lean_inc_ref(x_1026);
x_1042 = l_Array_append___redArg(x_1026, x_1041);
lean_dec_ref(x_1041);
lean_inc(x_1028);
lean_inc(x_1040);
x_1043 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1043, 0, x_1040);
lean_ctor_set(x_1043, 1, x_1028);
lean_ctor_set(x_1043, 2, x_1042);
if (lean_obj_tag(x_1035) == 1)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1044 = lean_ctor_get(x_1035, 0);
lean_inc(x_1044);
lean_dec_ref(x_1035);
x_1045 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30));
lean_inc_ref(x_1038);
x_1046 = l_Lean_Name_mkStr4(x_4, x_5, x_1038, x_1045);
x_1047 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31));
lean_inc(x_1040);
x_1048 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1048, 0, x_1040);
lean_ctor_set(x_1048, 1, x_1047);
lean_inc_ref(x_1026);
x_1049 = l_Array_append___redArg(x_1026, x_1044);
lean_dec(x_1044);
lean_inc(x_1028);
lean_inc(x_1040);
x_1050 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1050, 0, x_1040);
lean_ctor_set(x_1050, 1, x_1028);
lean_ctor_set(x_1050, 2, x_1049);
x_1051 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32));
lean_inc(x_1040);
x_1052 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1052, 0, x_1040);
lean_ctor_set(x_1052, 1, x_1051);
lean_inc(x_1040);
x_1053 = l_Lean_Syntax_node3(x_1040, x_1046, x_1048, x_1050, x_1052);
x_1054 = l_Array_mkArray1___redArg(x_1053);
x_981 = x_1023;
x_982 = x_1024;
x_983 = x_1043;
x_984 = x_1025;
x_985 = x_1026;
x_986 = x_1027;
x_987 = x_1028;
x_988 = x_1029;
x_989 = x_1030;
x_990 = x_1031;
x_991 = x_1032;
x_992 = x_1033;
x_993 = x_1034;
x_994 = x_1036;
x_995 = x_1037;
x_996 = x_1038;
x_997 = x_1039;
x_998 = x_1040;
x_999 = x_1054;
goto block_1022;
}
else
{
lean_object* x_1055; 
lean_dec(x_1035);
x_1055 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_981 = x_1023;
x_982 = x_1024;
x_983 = x_1043;
x_984 = x_1025;
x_985 = x_1026;
x_986 = x_1027;
x_987 = x_1028;
x_988 = x_1029;
x_989 = x_1030;
x_990 = x_1031;
x_991 = x_1032;
x_992 = x_1033;
x_993 = x_1034;
x_994 = x_1036;
x_995 = x_1037;
x_996 = x_1038;
x_997 = x_1039;
x_998 = x_1040;
x_999 = x_1055;
goto block_1022;
}
}
block_1095:
{
lean_object* x_1068; 
lean_inc_ref(x_1066);
lean_inc(x_1061);
x_1068 = l_Lean_evalPrec(x_1061, x_1066, x_1067);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
lean_dec_ref(x_1068);
x_1071 = lean_ctor_get(x_1066, 1);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1066, 2);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1066, 5);
lean_inc(x_1073);
lean_dec_ref(x_1066);
x_1074 = lean_unsigned_to_nat(7u);
x_1075 = l_Lean_Syntax_getArg(x_1, x_1074);
x_1076 = lean_unsigned_to_nat(9u);
x_1077 = l_Lean_Syntax_getArg(x_1, x_1076);
lean_dec(x_1);
x_1078 = lean_nat_add(x_1069, x_1058);
lean_dec(x_1069);
x_1079 = l_Nat_reprFast(x_1078);
x_1080 = lean_box(2);
x_1081 = l_Lean_Syntax_mkNumLit(x_1079, x_1080);
x_1082 = 0;
x_1083 = l_Lean_SourceInfo_fromRef(x_1073, x_1082);
lean_dec(x_1073);
x_1084 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33));
x_1085 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34));
x_1086 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36));
x_1087 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
if (lean_obj_tag(x_1060) == 1)
{
lean_object* x_1088; lean_object* x_1089; 
x_1088 = lean_ctor_get(x_1060, 0);
lean_inc(x_1088);
lean_dec_ref(x_1060);
x_1089 = l_Array_mkArray1___redArg(x_1088);
x_1023 = x_1072;
x_1024 = x_1065;
x_1025 = x_1077;
x_1026 = x_1087;
x_1027 = x_1085;
x_1028 = x_1086;
x_1029 = x_1070;
x_1030 = x_1064;
x_1031 = x_1063;
x_1032 = x_1075;
x_1033 = x_1057;
x_1034 = x_1071;
x_1035 = x_1059;
x_1036 = x_1061;
x_1037 = x_1084;
x_1038 = x_1062;
x_1039 = x_1081;
x_1040 = x_1083;
x_1041 = x_1089;
goto block_1056;
}
else
{
lean_object* x_1090; 
lean_dec(x_1060);
x_1090 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
x_1023 = x_1072;
x_1024 = x_1065;
x_1025 = x_1077;
x_1026 = x_1087;
x_1027 = x_1085;
x_1028 = x_1086;
x_1029 = x_1070;
x_1030 = x_1064;
x_1031 = x_1063;
x_1032 = x_1075;
x_1033 = x_1057;
x_1034 = x_1071;
x_1035 = x_1059;
x_1036 = x_1061;
x_1037 = x_1084;
x_1038 = x_1062;
x_1039 = x_1081;
x_1040 = x_1083;
x_1041 = x_1090;
goto block_1056;
}
}
else
{
uint8_t x_1091; 
lean_dec_ref(x_1066);
lean_dec(x_1065);
lean_dec(x_1064);
lean_dec(x_1063);
lean_dec_ref(x_1062);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1059);
lean_dec(x_1057);
lean_dec(x_1);
x_1091 = !lean_is_exclusive(x_1068);
if (x_1091 == 0)
{
return x_1068;
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1092 = lean_ctor_get(x_1068, 0);
x_1093 = lean_ctor_get(x_1068, 1);
lean_inc(x_1093);
lean_inc(x_1092);
lean_dec(x_1068);
x_1094 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1094, 0, x_1092);
lean_ctor_set(x_1094, 1, x_1093);
return x_1094;
}
}
}
block_1119:
{
lean_object* x_1107; lean_object* x_1108; uint8_t x_1109; 
x_1107 = lean_unsigned_to_nat(6u);
x_1108 = l_Lean_Syntax_getArg(x_1, x_1107);
x_1109 = l_Lean_Syntax_isNone(x_1108);
if (x_1109 == 0)
{
uint8_t x_1110; 
lean_inc(x_1108);
x_1110 = l_Lean_Syntax_matchesNull(x_1108, x_1097);
if (x_1110 == 0)
{
lean_object* x_1111; 
lean_dec(x_1108);
lean_dec_ref(x_1105);
lean_dec(x_1104);
lean_dec(x_1103);
lean_dec_ref(x_1102);
lean_dec(x_1101);
lean_dec(x_1100);
lean_dec(x_1098);
lean_dec(x_1096);
lean_dec(x_1);
x_1111 = l_Lean_Macro_throwUnsupported___redArg(x_1106);
return x_1111;
}
else
{
lean_object* x_1112; lean_object* x_1113; uint8_t x_1114; 
x_1112 = l_Lean_Syntax_getArg(x_1108, x_274);
lean_dec(x_1108);
x_1113 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20));
lean_inc(x_1112);
x_1114 = l_Lean_Syntax_isOfKind(x_1112, x_1113);
if (x_1114 == 0)
{
lean_object* x_1115; 
lean_dec(x_1112);
lean_dec_ref(x_1105);
lean_dec(x_1104);
lean_dec(x_1103);
lean_dec_ref(x_1102);
lean_dec(x_1101);
lean_dec(x_1100);
lean_dec(x_1098);
lean_dec(x_1096);
lean_dec(x_1);
x_1115 = l_Lean_Macro_throwUnsupported___redArg(x_1106);
return x_1115;
}
else
{
lean_object* x_1116; lean_object* x_1117; 
x_1116 = l_Lean_Syntax_getArg(x_1112, x_1099);
lean_dec(x_1112);
x_1117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1117, 0, x_1116);
x_1057 = x_1096;
x_1058 = x_1097;
x_1059 = x_1098;
x_1060 = x_1101;
x_1061 = x_1100;
x_1062 = x_1102;
x_1063 = x_1103;
x_1064 = x_1104;
x_1065 = x_1117;
x_1066 = x_1105;
x_1067 = x_1106;
goto block_1095;
}
}
}
else
{
lean_object* x_1118; 
lean_dec(x_1108);
x_1118 = lean_box(0);
x_1057 = x_1096;
x_1058 = x_1097;
x_1059 = x_1098;
x_1060 = x_1101;
x_1061 = x_1100;
x_1062 = x_1102;
x_1063 = x_1103;
x_1064 = x_1104;
x_1065 = x_1118;
x_1066 = x_1105;
x_1067 = x_1106;
goto block_1095;
}
}
block_1237:
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; 
x_1125 = lean_unsigned_to_nat(2u);
x_1126 = l_Lean_Syntax_getArg(x_1, x_1125);
x_1127 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__38));
x_1128 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__40));
lean_inc(x_1126);
x_1129 = l_Lean_Syntax_isOfKind(x_1126, x_1128);
if (x_1129 == 0)
{
lean_object* x_1130; 
lean_dec(x_1126);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1130 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1130;
}
else
{
lean_object* x_1131; uint8_t x_1132; 
x_1131 = l_Lean_Syntax_getArg(x_1126, x_274);
lean_dec(x_1126);
x_1132 = l_Lean_Syntax_matchesNull(x_1131, x_274);
if (x_1132 == 0)
{
lean_object* x_1133; 
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1133 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1133;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; uint8_t x_1137; 
x_1134 = lean_unsigned_to_nat(3u);
x_1135 = l_Lean_Syntax_getArg(x_1, x_1134);
x_1136 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__42));
lean_inc(x_1135);
x_1137 = l_Lean_Syntax_isOfKind(x_1135, x_1136);
if (x_1137 == 0)
{
lean_object* x_1138; uint8_t x_1139; 
x_1138 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__44));
lean_inc(x_1135);
x_1139 = l_Lean_Syntax_isOfKind(x_1135, x_1138);
if (x_1139 == 0)
{
lean_object* x_1140; uint8_t x_1141; 
x_1140 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__46));
lean_inc(x_1135);
x_1141 = l_Lean_Syntax_isOfKind(x_1135, x_1140);
if (x_1141 == 0)
{
lean_object* x_1142; uint8_t x_1143; 
x_1142 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__48));
lean_inc(x_1135);
x_1143 = l_Lean_Syntax_isOfKind(x_1135, x_1142);
if (x_1143 == 0)
{
lean_object* x_1144; uint8_t x_1145; 
x_1144 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__50));
x_1145 = l_Lean_Syntax_isOfKind(x_1135, x_1144);
if (x_1145 == 0)
{
lean_object* x_1146; 
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1146 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1146;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; uint8_t x_1150; 
x_1147 = lean_unsigned_to_nat(4u);
x_1148 = l_Lean_Syntax_getArg(x_1, x_1147);
x_1149 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(x_1148);
x_1150 = l_Lean_Syntax_isOfKind(x_1148, x_1149);
if (x_1150 == 0)
{
lean_object* x_1151; 
lean_dec(x_1148);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1151 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1151;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; uint8_t x_1155; 
x_1152 = l_Lean_Syntax_getArg(x_1148, x_1120);
lean_dec(x_1148);
x_1153 = lean_unsigned_to_nat(5u);
x_1154 = l_Lean_Syntax_getArg(x_1, x_1153);
x_1155 = l_Lean_Syntax_isNone(x_1154);
if (x_1155 == 0)
{
uint8_t x_1156; 
lean_inc(x_1154);
x_1156 = l_Lean_Syntax_matchesNull(x_1154, x_1120);
if (x_1156 == 0)
{
lean_object* x_1157; 
lean_dec(x_1154);
lean_dec(x_1152);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1157 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1157;
}
else
{
lean_object* x_1158; lean_object* x_1159; uint8_t x_1160; 
x_1158 = l_Lean_Syntax_getArg(x_1154, x_274);
lean_dec(x_1154);
x_1159 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_1158);
x_1160 = l_Lean_Syntax_isOfKind(x_1158, x_1159);
if (x_1160 == 0)
{
lean_object* x_1161; 
lean_dec(x_1158);
lean_dec(x_1152);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1161 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1161;
}
else
{
lean_object* x_1162; lean_object* x_1163; 
x_1162 = l_Lean_Syntax_getArg(x_1158, x_1134);
lean_dec(x_1158);
x_1163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1163, 0, x_1162);
x_409 = x_1149;
x_410 = x_1128;
x_411 = x_1120;
x_412 = x_1122;
x_413 = x_1134;
x_414 = x_1121;
x_415 = x_1152;
x_416 = x_1127;
x_417 = x_1143;
x_418 = x_1163;
x_419 = x_1123;
x_420 = x_1124;
goto block_433;
}
}
}
else
{
lean_object* x_1164; 
lean_dec(x_1154);
x_1164 = lean_box(0);
x_409 = x_1149;
x_410 = x_1128;
x_411 = x_1120;
x_412 = x_1122;
x_413 = x_1134;
x_414 = x_1121;
x_415 = x_1152;
x_416 = x_1127;
x_417 = x_1143;
x_418 = x_1164;
x_419 = x_1123;
x_420 = x_1124;
goto block_433;
}
}
}
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; uint8_t x_1168; 
lean_dec(x_1135);
x_1165 = lean_unsigned_to_nat(4u);
x_1166 = l_Lean_Syntax_getArg(x_1, x_1165);
x_1167 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(x_1166);
x_1168 = l_Lean_Syntax_isOfKind(x_1166, x_1167);
if (x_1168 == 0)
{
lean_object* x_1169; 
lean_dec(x_1166);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1169 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1169;
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; uint8_t x_1173; 
x_1170 = l_Lean_Syntax_getArg(x_1166, x_1120);
lean_dec(x_1166);
x_1171 = lean_unsigned_to_nat(5u);
x_1172 = l_Lean_Syntax_getArg(x_1, x_1171);
x_1173 = l_Lean_Syntax_isNone(x_1172);
if (x_1173 == 0)
{
uint8_t x_1174; 
lean_inc(x_1172);
x_1174 = l_Lean_Syntax_matchesNull(x_1172, x_1120);
if (x_1174 == 0)
{
lean_object* x_1175; 
lean_dec(x_1172);
lean_dec(x_1170);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1175 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1175;
}
else
{
lean_object* x_1176; lean_object* x_1177; uint8_t x_1178; 
x_1176 = l_Lean_Syntax_getArg(x_1172, x_274);
lean_dec(x_1172);
x_1177 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_1176);
x_1178 = l_Lean_Syntax_isOfKind(x_1176, x_1177);
if (x_1178 == 0)
{
lean_object* x_1179; 
lean_dec(x_1176);
lean_dec(x_1170);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1179 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1179;
}
else
{
lean_object* x_1180; lean_object* x_1181; 
x_1180 = l_Lean_Syntax_getArg(x_1176, x_1134);
lean_dec(x_1176);
x_1181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1181, 0, x_1180);
x_568 = x_1128;
x_569 = x_1120;
x_570 = x_1122;
x_571 = x_1134;
x_572 = x_1170;
x_573 = x_1121;
x_574 = x_1167;
x_575 = x_1127;
x_576 = x_1141;
x_577 = x_1181;
x_578 = x_1123;
x_579 = x_1124;
goto block_592;
}
}
}
else
{
lean_object* x_1182; 
lean_dec(x_1172);
x_1182 = lean_box(0);
x_568 = x_1128;
x_569 = x_1120;
x_570 = x_1122;
x_571 = x_1134;
x_572 = x_1170;
x_573 = x_1121;
x_574 = x_1167;
x_575 = x_1127;
x_576 = x_1141;
x_577 = x_1182;
x_578 = x_1123;
x_579 = x_1124;
goto block_592;
}
}
}
}
else
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; 
lean_dec(x_1135);
x_1183 = lean_unsigned_to_nat(4u);
x_1184 = l_Lean_Syntax_getArg(x_1, x_1183);
x_1185 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(x_1184);
x_1186 = l_Lean_Syntax_isOfKind(x_1184, x_1185);
if (x_1186 == 0)
{
lean_object* x_1187; 
lean_dec(x_1184);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1187 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1187;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; uint8_t x_1191; 
x_1188 = l_Lean_Syntax_getArg(x_1184, x_1120);
lean_dec(x_1184);
x_1189 = lean_unsigned_to_nat(5u);
x_1190 = l_Lean_Syntax_getArg(x_1, x_1189);
x_1191 = l_Lean_Syntax_isNone(x_1190);
if (x_1191 == 0)
{
uint8_t x_1192; 
lean_inc(x_1190);
x_1192 = l_Lean_Syntax_matchesNull(x_1190, x_1120);
if (x_1192 == 0)
{
lean_object* x_1193; 
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1193 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1193;
}
else
{
lean_object* x_1194; lean_object* x_1195; uint8_t x_1196; 
x_1194 = l_Lean_Syntax_getArg(x_1190, x_274);
lean_dec(x_1190);
x_1195 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_1194);
x_1196 = l_Lean_Syntax_isOfKind(x_1194, x_1195);
if (x_1196 == 0)
{
lean_object* x_1197; 
lean_dec(x_1194);
lean_dec(x_1188);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1197 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1197;
}
else
{
lean_object* x_1198; lean_object* x_1199; 
x_1198 = l_Lean_Syntax_getArg(x_1194, x_1134);
lean_dec(x_1194);
x_1199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1199, 0, x_1198);
x_744 = x_1128;
x_745 = x_1185;
x_746 = x_1120;
x_747 = x_1139;
x_748 = x_1188;
x_749 = x_1122;
x_750 = x_1134;
x_751 = x_1121;
x_752 = x_1127;
x_753 = x_1199;
x_754 = x_1123;
x_755 = x_1124;
goto block_768;
}
}
}
else
{
lean_object* x_1200; 
lean_dec(x_1190);
x_1200 = lean_box(0);
x_744 = x_1128;
x_745 = x_1185;
x_746 = x_1120;
x_747 = x_1139;
x_748 = x_1188;
x_749 = x_1122;
x_750 = x_1134;
x_751 = x_1121;
x_752 = x_1127;
x_753 = x_1200;
x_754 = x_1123;
x_755 = x_1124;
goto block_768;
}
}
}
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; uint8_t x_1204; 
lean_dec(x_1135);
x_1201 = lean_unsigned_to_nat(4u);
x_1202 = l_Lean_Syntax_getArg(x_1, x_1201);
x_1203 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(x_1202);
x_1204 = l_Lean_Syntax_isOfKind(x_1202, x_1203);
if (x_1204 == 0)
{
lean_object* x_1205; 
lean_dec(x_1202);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1205 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1205;
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; uint8_t x_1209; 
x_1206 = l_Lean_Syntax_getArg(x_1202, x_1120);
lean_dec(x_1202);
x_1207 = lean_unsigned_to_nat(5u);
x_1208 = l_Lean_Syntax_getArg(x_1, x_1207);
x_1209 = l_Lean_Syntax_isNone(x_1208);
if (x_1209 == 0)
{
uint8_t x_1210; 
lean_inc(x_1208);
x_1210 = l_Lean_Syntax_matchesNull(x_1208, x_1120);
if (x_1210 == 0)
{
lean_object* x_1211; 
lean_dec(x_1208);
lean_dec(x_1206);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1211 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1211;
}
else
{
lean_object* x_1212; lean_object* x_1213; uint8_t x_1214; 
x_1212 = l_Lean_Syntax_getArg(x_1208, x_274);
lean_dec(x_1208);
x_1213 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_1212);
x_1214 = l_Lean_Syntax_isOfKind(x_1212, x_1213);
if (x_1214 == 0)
{
lean_object* x_1215; 
lean_dec(x_1212);
lean_dec(x_1206);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1215 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1215;
}
else
{
lean_object* x_1216; lean_object* x_1217; 
x_1216 = l_Lean_Syntax_getArg(x_1212, x_1134);
lean_dec(x_1212);
x_1217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1217, 0, x_1216);
x_920 = x_1128;
x_921 = x_1120;
x_922 = x_1122;
x_923 = x_1134;
x_924 = x_1137;
x_925 = x_1206;
x_926 = x_1121;
x_927 = x_1127;
x_928 = x_1203;
x_929 = x_1217;
x_930 = x_1123;
x_931 = x_1124;
goto block_944;
}
}
}
else
{
lean_object* x_1218; 
lean_dec(x_1208);
x_1218 = lean_box(0);
x_920 = x_1128;
x_921 = x_1120;
x_922 = x_1122;
x_923 = x_1134;
x_924 = x_1137;
x_925 = x_1206;
x_926 = x_1121;
x_927 = x_1127;
x_928 = x_1203;
x_929 = x_1218;
x_930 = x_1123;
x_931 = x_1124;
goto block_944;
}
}
}
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; 
lean_dec(x_1135);
x_1219 = lean_unsigned_to_nat(4u);
x_1220 = l_Lean_Syntax_getArg(x_1, x_1219);
x_1221 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52));
lean_inc(x_1220);
x_1222 = l_Lean_Syntax_isOfKind(x_1220, x_1221);
if (x_1222 == 0)
{
lean_object* x_1223; 
lean_dec(x_1220);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1223 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1223;
}
else
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; uint8_t x_1227; 
x_1224 = l_Lean_Syntax_getArg(x_1220, x_1120);
lean_dec(x_1220);
x_1225 = lean_unsigned_to_nat(5u);
x_1226 = l_Lean_Syntax_getArg(x_1, x_1225);
x_1227 = l_Lean_Syntax_isNone(x_1226);
if (x_1227 == 0)
{
uint8_t x_1228; 
lean_inc(x_1226);
x_1228 = l_Lean_Syntax_matchesNull(x_1226, x_1120);
if (x_1228 == 0)
{
lean_object* x_1229; 
lean_dec(x_1226);
lean_dec(x_1224);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1229 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1229;
}
else
{
lean_object* x_1230; lean_object* x_1231; uint8_t x_1232; 
x_1230 = l_Lean_Syntax_getArg(x_1226, x_274);
lean_dec(x_1226);
x_1231 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28));
lean_inc(x_1230);
x_1232 = l_Lean_Syntax_isOfKind(x_1230, x_1231);
if (x_1232 == 0)
{
lean_object* x_1233; 
lean_dec(x_1230);
lean_dec(x_1224);
lean_dec_ref(x_1123);
lean_dec(x_1122);
lean_dec(x_1121);
lean_dec(x_1);
x_1233 = l_Lean_Macro_throwUnsupported___redArg(x_1124);
return x_1233;
}
else
{
lean_object* x_1234; lean_object* x_1235; 
x_1234 = l_Lean_Syntax_getArg(x_1230, x_1134);
lean_dec(x_1230);
x_1235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1235, 0, x_1234);
x_1096 = x_1128;
x_1097 = x_1120;
x_1098 = x_1122;
x_1099 = x_1134;
x_1100 = x_1224;
x_1101 = x_1121;
x_1102 = x_1127;
x_1103 = x_1221;
x_1104 = x_1235;
x_1105 = x_1123;
x_1106 = x_1124;
goto block_1119;
}
}
}
else
{
lean_object* x_1236; 
lean_dec(x_1226);
x_1236 = lean_box(0);
x_1096 = x_1128;
x_1097 = x_1120;
x_1098 = x_1122;
x_1099 = x_1134;
x_1100 = x_1224;
x_1101 = x_1121;
x_1102 = x_1127;
x_1103 = x_1221;
x_1104 = x_1236;
x_1105 = x_1123;
x_1106 = x_1124;
goto block_1119;
}
}
}
}
}
}
block_1254:
{
lean_object* x_1241; lean_object* x_1242; uint8_t x_1243; 
x_1241 = lean_unsigned_to_nat(1u);
x_1242 = l_Lean_Syntax_getArg(x_1, x_1241);
x_1243 = l_Lean_Syntax_isNone(x_1242);
if (x_1243 == 0)
{
uint8_t x_1244; 
lean_inc(x_1242);
x_1244 = l_Lean_Syntax_matchesNull(x_1242, x_1241);
if (x_1244 == 0)
{
lean_object* x_1245; 
lean_dec(x_1242);
lean_dec_ref(x_1239);
lean_dec(x_1238);
lean_dec(x_1);
x_1245 = l_Lean_Macro_throwUnsupported___redArg(x_1240);
return x_1245;
}
else
{
lean_object* x_1246; lean_object* x_1247; uint8_t x_1248; 
x_1246 = l_Lean_Syntax_getArg(x_1242, x_274);
lean_dec(x_1242);
x_1247 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__53));
lean_inc(x_1246);
x_1248 = l_Lean_Syntax_isOfKind(x_1246, x_1247);
if (x_1248 == 0)
{
lean_object* x_1249; 
lean_dec(x_1246);
lean_dec_ref(x_1239);
lean_dec(x_1238);
lean_dec(x_1);
x_1249 = l_Lean_Macro_throwUnsupported___redArg(x_1240);
return x_1249;
}
else
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
x_1250 = l_Lean_Syntax_getArg(x_1246, x_1241);
lean_dec(x_1246);
x_1251 = l_Lean_Syntax_getArgs(x_1250);
lean_dec(x_1250);
x_1252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1252, 0, x_1251);
x_1120 = x_1241;
x_1121 = x_1238;
x_1122 = x_1252;
x_1123 = x_1239;
x_1124 = x_1240;
goto block_1237;
}
}
}
else
{
lean_object* x_1253; 
lean_dec(x_1242);
x_1253 = lean_box(0);
x_1120 = x_1241;
x_1121 = x_1238;
x_1122 = x_1253;
x_1123 = x_1239;
x_1124 = x_1240;
goto block_1237;
}
}
}
block_52:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_23 = l_Array_append___redArg(x_15, x_22);
lean_dec_ref(x_22);
lean_inc(x_20);
lean_inc(x_10);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_26 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__6;
x_27 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
x_28 = l_Lean_addMacroScope(x_21, x_27, x_16);
x_29 = lean_box(0);
lean_inc(x_10);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
lean_inc(x_8);
lean_inc_ref(x_30);
lean_inc(x_10);
x_31 = l_Lean_Syntax_node2(x_10, x_25, x_30, x_8);
lean_inc(x_20);
lean_inc(x_10);
x_32 = l_Lean_Syntax_node2(x_10, x_20, x_31, x_13);
x_33 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_10);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
x_35 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_36 = l_Lean_Name_mkStr4(x_4, x_5, x_17, x_35);
lean_inc(x_10);
x_37 = l_Lean_Syntax_node1(x_10, x_20, x_30);
lean_inc(x_10);
x_38 = l_Lean_Syntax_node2(x_10, x_36, x_14, x_37);
x_39 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
x_40 = lean_array_push(x_39, x_6);
x_41 = lean_array_push(x_40, x_19);
x_42 = lean_array_push(x_41, x_12);
x_43 = lean_array_push(x_42, x_18);
x_44 = lean_array_push(x_43, x_8);
x_45 = lean_array_push(x_44, x_9);
x_46 = lean_array_push(x_45, x_24);
x_47 = lean_array_push(x_46, x_32);
x_48 = lean_array_push(x_47, x_34);
x_49 = lean_array_push(x_48, x_38);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_7);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
block_99:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_70 = l_Array_append___redArg(x_65, x_69);
lean_dec_ref(x_69);
lean_inc(x_61);
lean_inc(x_64);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_61);
lean_ctor_set(x_71, 2, x_70);
x_72 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_73 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__6;
x_74 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7));
x_75 = l_Lean_addMacroScope(x_54, x_74, x_62);
x_76 = lean_box(0);
lean_inc(x_64);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_76);
lean_inc(x_56);
lean_inc_ref(x_77);
lean_inc(x_64);
x_78 = l_Lean_Syntax_node2(x_64, x_72, x_77, x_56);
lean_inc(x_61);
lean_inc(x_64);
x_79 = l_Lean_Syntax_node2(x_64, x_61, x_58, x_78);
x_80 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_64);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_64);
lean_ctor_set(x_81, 1, x_80);
x_82 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_83 = l_Lean_Name_mkStr4(x_4, x_5, x_67, x_82);
lean_inc(x_64);
x_84 = l_Lean_Syntax_node1(x_64, x_61, x_77);
lean_inc(x_64);
x_85 = l_Lean_Syntax_node2(x_64, x_83, x_60, x_84);
x_86 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
x_87 = lean_array_push(x_86, x_63);
x_88 = lean_array_push(x_87, x_57);
x_89 = lean_array_push(x_88, x_66);
x_90 = lean_array_push(x_89, x_59);
x_91 = lean_array_push(x_90, x_56);
x_92 = lean_array_push(x_91, x_55);
x_93 = lean_array_push(x_92, x_71);
x_94 = lean_array_push(x_93, x_79);
x_95 = lean_array_push(x_94, x_81);
x_96 = lean_array_push(x_95, x_85);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_64);
lean_ctor_set(x_97, 1, x_53);
lean_ctor_set(x_97, 2, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_68);
return x_98;
}
block_156:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_120 = l_Array_append___redArg(x_104, x_119);
lean_dec_ref(x_119);
lean_inc(x_102);
lean_inc(x_105);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_102);
lean_ctor_set(x_121, 2, x_120);
x_122 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_123 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
x_124 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13));
lean_inc(x_112);
lean_inc(x_116);
x_125 = l_Lean_addMacroScope(x_116, x_124, x_112);
x_126 = lean_box(0);
lean_inc(x_105);
x_127 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_127, 0, x_105);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set(x_127, 2, x_125);
lean_ctor_set(x_127, 3, x_126);
lean_inc(x_105);
x_128 = l_Lean_Syntax_node2(x_105, x_110, x_113, x_117);
lean_inc(x_102);
lean_inc(x_105);
x_129 = l_Lean_Syntax_node1(x_105, x_102, x_128);
lean_inc_ref(x_127);
lean_inc(x_105);
x_130 = l_Lean_Syntax_node2(x_105, x_122, x_127, x_129);
x_131 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
x_132 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__16));
x_133 = l_Lean_addMacroScope(x_116, x_132, x_112);
lean_inc(x_105);
x_134 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_134, 0, x_105);
lean_ctor_set(x_134, 1, x_131);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_126);
lean_inc(x_114);
lean_inc_ref(x_134);
lean_inc(x_105);
x_135 = l_Lean_Syntax_node2(x_105, x_122, x_134, x_114);
lean_inc(x_102);
lean_inc(x_105);
x_136 = l_Lean_Syntax_node3(x_105, x_102, x_130, x_106, x_135);
x_137 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_105);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_105);
lean_ctor_set(x_138, 1, x_137);
x_139 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_140 = l_Lean_Name_mkStr4(x_4, x_5, x_115, x_139);
lean_inc(x_105);
x_141 = l_Lean_Syntax_node2(x_105, x_102, x_127, x_134);
lean_inc(x_105);
x_142 = l_Lean_Syntax_node2(x_105, x_140, x_109, x_141);
x_143 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
x_144 = lean_array_push(x_143, x_108);
x_145 = lean_array_push(x_144, x_107);
x_146 = lean_array_push(x_145, x_101);
x_147 = lean_array_push(x_146, x_118);
x_148 = lean_array_push(x_147, x_114);
x_149 = lean_array_push(x_148, x_111);
x_150 = lean_array_push(x_149, x_121);
x_151 = lean_array_push(x_150, x_136);
x_152 = lean_array_push(x_151, x_138);
x_153 = lean_array_push(x_152, x_142);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_105);
lean_ctor_set(x_154, 1, x_103);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_100);
return x_155;
}
block_213:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_177 = l_Array_append___redArg(x_160, x_176);
lean_dec_ref(x_176);
lean_inc(x_170);
lean_inc(x_159);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_159);
lean_ctor_set(x_178, 1, x_170);
lean_ctor_set(x_178, 2, x_177);
x_179 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_180 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
x_181 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13));
lean_inc(x_174);
lean_inc(x_168);
x_182 = l_Lean_addMacroScope(x_168, x_181, x_174);
x_183 = lean_box(0);
lean_inc(x_159);
x_184 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_184, 0, x_159);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set(x_184, 2, x_182);
lean_ctor_set(x_184, 3, x_183);
lean_inc(x_159);
x_185 = l_Lean_Syntax_node2(x_159, x_167, x_165, x_158);
lean_inc(x_170);
lean_inc(x_159);
x_186 = l_Lean_Syntax_node1(x_159, x_170, x_185);
lean_inc(x_186);
lean_inc_ref(x_184);
lean_inc(x_159);
x_187 = l_Lean_Syntax_node2(x_159, x_179, x_184, x_186);
x_188 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
x_189 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__16));
x_190 = l_Lean_addMacroScope(x_168, x_189, x_174);
lean_inc(x_159);
x_191 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_191, 0, x_159);
lean_ctor_set(x_191, 1, x_188);
lean_ctor_set(x_191, 2, x_190);
lean_ctor_set(x_191, 3, x_183);
lean_inc_ref(x_191);
lean_inc(x_159);
x_192 = l_Lean_Syntax_node2(x_159, x_179, x_191, x_186);
lean_inc(x_170);
lean_inc(x_159);
x_193 = l_Lean_Syntax_node3(x_159, x_170, x_187, x_173, x_192);
x_194 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_159);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_159);
lean_ctor_set(x_195, 1, x_194);
x_196 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_197 = l_Lean_Name_mkStr4(x_4, x_5, x_175, x_196);
lean_inc(x_159);
x_198 = l_Lean_Syntax_node2(x_159, x_170, x_184, x_191);
lean_inc(x_159);
x_199 = l_Lean_Syntax_node2(x_159, x_197, x_169, x_198);
x_200 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
x_201 = lean_array_push(x_200, x_162);
x_202 = lean_array_push(x_201, x_163);
x_203 = lean_array_push(x_202, x_161);
x_204 = lean_array_push(x_203, x_164);
x_205 = lean_array_push(x_204, x_157);
x_206 = lean_array_push(x_205, x_166);
x_207 = lean_array_push(x_206, x_178);
x_208 = lean_array_push(x_207, x_193);
x_209 = lean_array_push(x_208, x_195);
x_210 = lean_array_push(x_209, x_199);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_159);
lean_ctor_set(x_211, 1, x_171);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_172);
return x_212;
}
block_270:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_234 = l_Array_append___redArg(x_221, x_233);
lean_dec_ref(x_233);
lean_inc(x_224);
lean_inc(x_231);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set(x_235, 1, x_224);
lean_ctor_set(x_235, 2, x_234);
x_236 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4));
x_237 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
x_238 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13));
lean_inc(x_215);
lean_inc(x_229);
x_239 = l_Lean_addMacroScope(x_229, x_238, x_215);
x_240 = lean_box(0);
lean_inc(x_231);
x_241 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_241, 0, x_231);
lean_ctor_set(x_241, 1, x_237);
lean_ctor_set(x_241, 2, x_239);
lean_ctor_set(x_241, 3, x_240);
lean_inc(x_222);
lean_inc_ref(x_241);
lean_inc(x_231);
x_242 = l_Lean_Syntax_node2(x_231, x_236, x_241, x_222);
x_243 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
x_244 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__16));
x_245 = l_Lean_addMacroScope(x_229, x_244, x_215);
lean_inc(x_231);
x_246 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_246, 0, x_231);
lean_ctor_set(x_246, 1, x_243);
lean_ctor_set(x_246, 2, x_245);
lean_ctor_set(x_246, 3, x_240);
lean_inc(x_231);
x_247 = l_Lean_Syntax_node2(x_231, x_226, x_223, x_232);
lean_inc(x_224);
lean_inc(x_231);
x_248 = l_Lean_Syntax_node1(x_231, x_224, x_247);
lean_inc_ref(x_246);
lean_inc(x_231);
x_249 = l_Lean_Syntax_node2(x_231, x_236, x_246, x_248);
lean_inc(x_224);
lean_inc(x_231);
x_250 = l_Lean_Syntax_node3(x_231, x_224, x_242, x_227, x_249);
x_251 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8));
lean_inc(x_231);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_231);
lean_ctor_set(x_252, 1, x_251);
x_253 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9));
x_254 = l_Lean_Name_mkStr4(x_4, x_5, x_230, x_253);
lean_inc(x_231);
x_255 = l_Lean_Syntax_node2(x_231, x_224, x_241, x_246);
lean_inc(x_231);
x_256 = l_Lean_Syntax_node2(x_231, x_254, x_218, x_255);
x_257 = l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
x_258 = lean_array_push(x_257, x_217);
x_259 = lean_array_push(x_258, x_216);
x_260 = lean_array_push(x_259, x_220);
x_261 = lean_array_push(x_260, x_214);
x_262 = lean_array_push(x_261, x_222);
x_263 = lean_array_push(x_262, x_228);
x_264 = lean_array_push(x_263, x_235);
x_265 = lean_array_push(x_264, x_250);
x_266 = lean_array_push(x_265, x_252);
x_267 = lean_array_push(x_266, x_256);
x_268 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_268, 0, x_231);
lean_ctor_set(x_268, 1, x_219);
lean_ctor_set(x_268, 2, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_225);
return x_269;
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
x_3 = ((lean_object*)(l_Lean_Elab_Command_expandMixfix___lam__0___closed__18));
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
lean_object* initialize_Lean_Elab_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Mixfix(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandMixfix___lam__0___closed__6 = _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandMixfix___lam__0___closed__6);
l_Lean_Elab_Command_expandMixfix___lam__0___closed__10 = _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10);
l_Lean_Elab_Command_expandMixfix___lam__0___closed__12 = _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12);
l_Lean_Elab_Command_expandMixfix___lam__0___closed__15 = _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15);
l_Lean_Elab_Command_expandMixfix___lam__0___closed__25 = _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25);
l_Lean_Elab_Command_expandMixfix___lam__0___closed__37 = _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__37();
lean_mark_persistent(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37);
if (builtin) {res = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
