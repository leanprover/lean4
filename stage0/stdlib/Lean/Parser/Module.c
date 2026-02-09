// Lean compiler output
// Module: Lean.Parser.Module
// Imports: public import Lean.Parser.Command import Init.While
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
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__0 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__1 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__2 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__3 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__4 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Parser_Module_moduleTk___closed__5;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__6 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value;
lean_object* l_Lean_Parser_symbol(lean_object*);
static lean_object* l_Lean_Parser_Module_moduleTk___closed__7;
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_moduleTk___closed__8;
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_moduleTk___closed__9;
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_moduleTk___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk;
static const lean_string_object l_Lean_Parser_Module_prelude___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_Parser_Module_prelude___closed__0 = (const lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l_Lean_Parser_Module_prelude___closed__1 = (const lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value;
static lean_object* l_Lean_Parser_Module_prelude___closed__2;
static lean_object* l_Lean_Parser_Module_prelude___closed__3;
static lean_object* l_Lean_Parser_Module_prelude___closed__4;
static lean_object* l_Lean_Parser_Module_prelude___closed__5;
static lean_object* l_Lean_Parser_Module_prelude___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude;
static const lean_string_object l_Lean_Parser_Module_public___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Parser_Module_public___closed__0 = (const lean_object*)&l_Lean_Parser_Module_public___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l_Lean_Parser_Module_public___closed__1 = (const lean_object*)&l_Lean_Parser_Module_public___closed__1_value;
static lean_object* l_Lean_Parser_Module_public___closed__2;
static lean_object* l_Lean_Parser_Module_public___closed__3;
static lean_object* l_Lean_Parser_Module_public___closed__4;
static lean_object* l_Lean_Parser_Module_public___closed__5;
static lean_object* l_Lean_Parser_Module_public___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public;
static const lean_string_object l_Lean_Parser_Module_meta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Parser_Module_meta___closed__0 = (const lean_object*)&l_Lean_Parser_Module_meta___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l_Lean_Parser_Module_meta___closed__1 = (const lean_object*)&l_Lean_Parser_Module_meta___closed__1_value;
static lean_object* l_Lean_Parser_Module_meta___closed__2;
static lean_object* l_Lean_Parser_Module_meta___closed__3;
static lean_object* l_Lean_Parser_Module_meta___closed__4;
static lean_object* l_Lean_Parser_Module_meta___closed__5;
static lean_object* l_Lean_Parser_Module_meta___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta;
static const lean_string_object l_Lean_Parser_Module_all___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Parser_Module_all___closed__0 = (const lean_object*)&l_Lean_Parser_Module_all___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l_Lean_Parser_Module_all___closed__1 = (const lean_object*)&l_Lean_Parser_Module_all___closed__1_value;
static lean_object* l_Lean_Parser_Module_all___closed__2;
static lean_object* l_Lean_Parser_Module_all___closed__3;
static lean_object* l_Lean_Parser_Module_all___closed__4;
static lean_object* l_Lean_Parser_Module_all___closed__5;
static lean_object* l_Lean_Parser_Module_all___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all;
static const lean_string_object l_Lean_Parser_Module_import___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_Lean_Parser_Module_import___closed__0 = (const lean_object*)&l_Lean_Parser_Module_import___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l_Lean_Parser_Module_import___closed__1 = (const lean_object*)&l_Lean_Parser_Module_import___closed__1_value;
static lean_object* l_Lean_Parser_Module_import___closed__2;
lean_object* l_Lean_Parser_optional(lean_object*);
static lean_object* l_Lean_Parser_Module_import___closed__3;
static lean_object* l_Lean_Parser_Module_import___closed__4;
static const lean_string_object l_Lean_Parser_Module_import___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l_Lean_Parser_Module_import___closed__5 = (const lean_object*)&l_Lean_Parser_Module_import___closed__5_value;
static lean_object* l_Lean_Parser_Module_import___closed__6;
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import___closed__7;
static lean_object* l_Lean_Parser_Module_import___closed__8;
lean_object* l_Lean_Parser_atomic(lean_object*);
static lean_object* l_Lean_Parser_Module_import___closed__9;
static lean_object* l_Lean_Parser_Module_import___closed__10;
extern lean_object* l_Lean_Parser_identWithPartialTrailingDot;
static lean_object* l_Lean_Parser_Module_import___closed__11;
static lean_object* l_Lean_Parser_Module_import___closed__12;
static lean_object* l_Lean_Parser_Module_import___closed__13;
static lean_object* l_Lean_Parser_Module_import___closed__14;
static lean_object* l_Lean_Parser_Module_import___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import;
static const lean_string_object l_Lean_Parser_Module_header___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Parser_Module_header___closed__0 = (const lean_object*)&l_Lean_Parser_Module_header___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Parser_Module_header___closed__1 = (const lean_object*)&l_Lean_Parser_Module_header___closed__1_value;
static lean_object* l_Lean_Parser_Module_header___closed__2;
extern lean_object* l_Lean_Parser_skip;
static lean_object* l_Lean_Parser_Module_header___closed__3;
static lean_object* l_Lean_Parser_Module_header___closed__4;
static lean_object* l_Lean_Parser_Module_header___closed__5;
static lean_object* l_Lean_Parser_Module_header___closed__6;
static lean_object* l_Lean_Parser_Module_header___closed__7;
static lean_object* l_Lean_Parser_Module_header___closed__8;
lean_object* l_Lean_Parser_many(lean_object*);
static lean_object* l_Lean_Parser_Module_header___closed__9;
static lean_object* l_Lean_Parser_Module_header___closed__10;
static lean_object* l_Lean_Parser_Module_header___closed__11;
static lean_object* l_Lean_Parser_Module_header___closed__12;
static lean_object* l_Lean_Parser_Module_header___closed__13;
static lean_object* l_Lean_Parser_Module_header___closed__14;
static lean_object* l_Lean_Parser_Module_header___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_moduleTk_formatter___closed__0;
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_moduleTk_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_formatter___closed__1_value;
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_moduleTk_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_formatter___closed__2_value;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 81, 79, 40, 155, 75, 46, 100)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_prelude_formatter___closed__0;
static const lean_closure_object l_Lean_Parser_Module_prelude_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_prelude_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_prelude_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_prelude_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_prelude_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 131, 178, 125, 52, 15, 11, 203)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_public_formatter___closed__0;
static const lean_closure_object l_Lean_Parser_Module_public_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_public_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_public_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_public_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_public_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_public_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_public_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 212, 57, 147, 153, 56, 10, 5)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_meta_formatter___closed__0;
static const lean_closure_object l_Lean_Parser_Module_meta_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_meta_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_meta_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_meta_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_meta_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_meta_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_meta_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 184, 202, 195, 54, 104, 118, 145)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_all_formatter___closed__0;
static const lean_closure_object l_Lean_Parser_Module_all_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_all_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_all_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_all_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_all_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_all_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_all_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 99, 131, 63, 105, 143, 101, 58)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__0;
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__1;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__2;
static const lean_closure_object l_Lean_Parser_Module_import_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__5_value)} };
static const lean_object* l_Lean_Parser_Module_import_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Module_import_formatter___closed__3_value;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__4;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__5;
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_formatter___closed__6;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__7;
lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_import_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_import_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Module_import_formatter___closed__8_value;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__9;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__10;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 109, 123, 234, 127, 180, 211, 104)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__0;
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__1;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__2;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__3;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__4;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__5;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__6;
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_formatter___closed__7;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__8;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__9;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__10;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 160, 40, 95, 57, 209, 137, 179)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___boxed(lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_object* l_Lean_Parser_Module_module_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__1;
lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_module_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_commandParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_module_formatter___closed__2_value;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__3;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__4;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__5;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 14, 206, 143, 52, 229, 209, 241)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___boxed(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0;
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 114, 81, 186, 242, 59, 227, 110)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__0;
static const lean_closure_object l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 254, 166, 235, 232, 231, 221, 239)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_public_parenthesizer___closed__0;
static const lean_closure_object l_Lean_Parser_Module_public_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_public_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_public_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_public_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_public_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_public_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_public_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 31, 175, 191, 217, 184, 6, 227)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_meta_parenthesizer___closed__0;
static const lean_closure_object l_Lean_Parser_Module_meta_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_meta_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_meta_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_meta_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_meta_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_meta_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_meta_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 15, 60, 11, 40, 43, 177, 15)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_all_parenthesizer___closed__0;
static const lean_closure_object l_Lean_Parser_Module_all_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_all_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_all_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_all_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_all_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_all_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_all_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 77, 255, 78, 93, 172, 67, 172)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__0;
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__2;
static const lean_closure_object l_Lean_Parser_Module_import_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__5_value)} };
static const lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Module_import_parenthesizer___closed__3_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__5;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__6;
lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_import_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Module_import_parenthesizer___closed__7_value;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__8;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__9;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 202, 16, 12, 219, 214, 31, 155)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__0;
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_header_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppLine_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__1_value;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__3;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__5;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__6;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__7;
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__8;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__9;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__10;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__11;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 253, 229, 230, 227, 57, 31, 73)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__0;
lean_object* l_Lean_Parser_commandParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_module_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_commandParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__1_value;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__3;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_ctor_object l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 111, 56, 211, 136, 139, 180, 239)}};
static const lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___boxed(lean_object*);
static lean_object* l_Lean_Parser_Module_module___closed__0;
static const lean_string_object l_Lean_Parser_Module_module___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Parser_Module_module___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_module___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Parser_Module_module___closed__2 = (const lean_object*)&l_Lean_Parser_Module_module___closed__2_value;
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_module___closed__3;
static lean_object* l_Lean_Parser_Module_module___closed__4;
static lean_object* l_Lean_Parser_Module_module___closed__5;
static lean_object* l_Lean_Parser_Module_module___closed__6;
static lean_object* l_Lean_Parser_Module_module___closed__7;
static lean_object* l_Lean_Parser_Module_module___closed__8;
static lean_object* l_Lean_Parser_Module_module___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module;
lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_object* l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(lean_object*);
static const lean_string_object l_Lean_Parser_Module_updateTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Parser.Module"};
static const lean_object* l_Lean_Parser_Module_updateTokens___closed__0 = (const lean_object*)&l_Lean_Parser_Module_updateTokens___closed__0_value;
static const lean_string_object l_Lean_Parser_Module_updateTokens___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Parser.Module.updateTokens"};
static const lean_object* l_Lean_Parser_Module_updateTokens___closed__1 = (const lean_object*)&l_Lean_Parser_Module_updateTokens___closed__1_value;
static const lean_string_object l_Lean_Parser_Module_updateTokens___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Parser_Module_updateTokens___closed__2 = (const lean_object*)&l_Lean_Parser_Module_updateTokens___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Module_updateTokens___closed__3;
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object*);
static const lean_ctor_object l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_instInhabitedModuleParserState_default___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedModuleParserState_default = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedModuleParserState = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
lean_object* l_Subarray_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected identifier"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unexpected token '"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unexpected token"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4_value;
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "cannot use `import all` without `module`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "cannot use `meta import` without `module`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "cannot use `all` with `public import`; consider using separate `public import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` and `import all "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 107, .m_capacity = 107, .m_length = 106, .m_data = "` directives in order to import public data into the public scope and private data into the private scope."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "cannot use `public import` without `module`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_parseHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_parseHeader___closed__0 = (const lean_object*)&l_Lean_Parser_parseHeader___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Parser_parseHeader___closed__1;
static lean_object* l_Lean_Parser_parseHeader___closed__2;
static lean_object* l_Lean_Parser_parseHeader___closed__3;
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_Parser_parseHeader___closed__4;
lean_object* lean_mk_empty_environment(uint32_t);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eoi"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__3_value),LEAN_SCALAR_PTR_LITERAL(26, 206, 8, 118, 9, 188, 233, 7)}};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4_value;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object*);
static const lean_string_object l_Lean_Parser_isTerminalCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l_Lean_Parser_isTerminalCommand___closed__0 = (const lean_object*)&l_Lean_Parser_isTerminalCommand___closed__0_value;
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 245, 50, 125, 205, 155, 109, 0)}};
static const lean_object* l_Lean_Parser_isTerminalCommand___closed__1 = (const lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value;
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 144, 26, 198, 154, 96, 74, 167)}};
static const lean_object* l_Lean_Parser_isTerminalCommand___closed__2 = (const lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object*);
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0;
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_tokenFn, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1_value;
lean_object* l_Char_utf8Size(uint32_t);
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2;
extern lean_object* l_Lean_Parser_SyntaxStack_empty;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0;
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "failed to parse file"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_testParseModule___closed__0;
static lean_object* l_Lean_Parser_testParseModule___closed__1;
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_mkListNode(lean_object*);
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__5() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_4 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__3));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_moduleTk___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_moduleTk___closed__8;
x_2 = l_Lean_Parser_Module_moduleTk___closed__5;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_moduleTk___closed__9;
x_2 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_moduleTk___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_prelude___closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__4;
x_2 = l_Lean_Parser_Module_prelude___closed__2;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__5;
x_2 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_prelude___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_public___closed__0));
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_public___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_public___closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_public___closed__4;
x_2 = l_Lean_Parser_Module_public___closed__2;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_public___closed__5;
x_2 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_public() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_public___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__0));
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_meta___closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_meta___closed__4;
x_2 = l_Lean_Parser_Module_meta___closed__2;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_meta___closed__5;
x_2 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_meta___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_all___closed__0));
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_all___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_all___closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_all___closed__4;
x_2 = l_Lean_Parser_Module_all___closed__2;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_all___closed__5;
x_2 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_all() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_all___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_import___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_public;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_meta;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import___closed__5));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__6;
x_2 = l_Lean_Parser_Module_import___closed__4;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__7;
x_2 = l_Lean_Parser_Module_import___closed__3;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___closed__8;
x_2 = l_Lean_Parser_atomic(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_all;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot;
x_2 = l_Lean_Parser_Module_import___closed__10;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__11;
x_2 = l_Lean_Parser_Module_import___closed__9;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import___closed__12;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__13;
x_2 = l_Lean_Parser_Module_import___closed__2;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__14;
x_2 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_import___closed__15;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_header___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_skip;
x_2 = l_Lean_Parser_andthen(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__3;
x_2 = l_Lean_Parser_Module_moduleTk;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header___closed__4;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_skip;
x_2 = l_Lean_Parser_Module_prelude;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header___closed__6;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_skip;
x_2 = l_Lean_Parser_Module_import;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header___closed__8;
x_2 = l_Lean_Parser_many(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_skip;
x_2 = l_Lean_Parser_Module_header___closed__9;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__10;
x_2 = l_Lean_Parser_Module_header___closed__7;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__11;
x_2 = l_Lean_Parser_Module_header___closed__5;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___closed__12;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__13;
x_2 = l_Lean_Parser_Module_header___closed__2;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__14;
x_2 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_header___closed__15;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk_formatter___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_4 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__3));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_moduleTk_formatter___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_moduleTk_formatter___closed__2));
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_moduleTk_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_formatter___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_prelude_formatter___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_prelude_formatter___closed__2));
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_prelude_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_public_formatter___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_public___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_public_formatter___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_public_formatter___closed__2));
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_public_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta_formatter___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_meta_formatter___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_meta_formatter___closed__2));
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_meta_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_all_formatter___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_all___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_all_formatter___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_all_formatter___closed__2));
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_all_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_import___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__3));
x_2 = l_Lean_Parser_Module_import_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_formatter___closed__4;
x_2 = l_Lean_Parser_Module_import_formatter___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__8));
x_2 = l_Lean_Parser_Module_import_formatter___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_formatter___closed__9;
x_2 = l_Lean_Parser_Module_import_formatter___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import_formatter___closed__10;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_import_formatter___closed__0;
x_7 = l_Lean_Parser_Module_import_formatter___closed__11;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_import_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_header___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__6;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_2 = l_Lean_Parser_Module_header_formatter___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__8;
x_2 = l_Lean_Parser_Module_header_formatter___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__9;
x_2 = l_Lean_Parser_Module_header_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__10;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_header_formatter___closed__0;
x_7 = l_Lean_Parser_Module_header_formatter___closed__11;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_header_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_formatter___closed__1;
x_2 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module_formatter___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_module_formatter___closed__1;
x_7 = l_Lean_Parser_Module_module_formatter___closed__6;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_module_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_4 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__3));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_moduleTk_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_prelude_parenthesizer___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_prelude_parenthesizer___closed__2));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_prelude_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_public_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_public___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_public_parenthesizer___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_public_parenthesizer___closed__2));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_public_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_meta_parenthesizer___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_meta_parenthesizer___closed__2));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_meta_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_all_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_Module_all___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_all_parenthesizer___closed__0;
x_7 = ((lean_object*)(l_Lean_Parser_Module_all_parenthesizer___closed__2));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_all_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_Module_import_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_import___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_parenthesizer___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_parenthesizer___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__3));
x_2 = l_Lean_Parser_Module_import_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_parenthesizer___closed__4;
x_2 = l_Lean_Parser_Module_import_parenthesizer___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__7));
x_2 = l_Lean_Parser_Module_import_parenthesizer___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import_parenthesizer___closed__8;
x_2 = l_Lean_Parser_Module_import_parenthesizer___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import_parenthesizer___closed__9;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_import_parenthesizer___closed__0;
x_7 = l_Lean_Parser_Module_import_parenthesizer___closed__10;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_import_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_header___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
x_2 = l_Lean_Parser_Module_header_parenthesizer___closed__8;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__9;
x_2 = l_Lean_Parser_Module_header_parenthesizer___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__10;
x_2 = l_Lean_Parser_Module_header_parenthesizer___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__11;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_header_parenthesizer___closed__0;
x_7 = l_Lean_Parser_Module_header_parenthesizer___closed__12;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_header_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header_parenthesizer___closed__2;
x_2 = ((lean_object*)(l_Lean_Parser_Module_module_parenthesizer___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_module_parenthesizer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module_parenthesizer___closed__4;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Module_module_parenthesizer___closed__0;
x_7 = l_Lean_Parser_Module_module_parenthesizer___closed__5;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_module_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = ((lean_object*)(l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Parser_Module_module___closed__2));
x_3 = l_Lean_Parser_categoryParser(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__3;
x_2 = l_Lean_Parser_Module_module___closed__3;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_module___closed__4;
x_2 = l_Lean_Parser_many(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___closed__5;
x_2 = l_Lean_Parser_Module_header;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_module___closed__6;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___closed__7;
x_2 = l_Lean_Parser_Module_module___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_module___closed__8;
x_2 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_module___closed__9;
return x_1;
}
}
static lean_object* _init_l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_updateTokens___closed__2));
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_unsigned_to_nat(42u);
x_4 = ((lean_object*)(l_Lean_Parser_Module_updateTokens___closed__1));
x_5 = ((lean_object*)(l_Lean_Parser_Module_updateTokens___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_Module_header;
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = l_Lean_Parser_addParserTokens(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_4);
x_5 = l_Lean_Parser_Module_updateTokens___closed__3;
x_6 = l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = l_Subarray_get___redArg(x_1, x_7);
x_9 = l_Lean_Syntax_getTailInfo(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_dec(x_9);
x_2 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_SyntaxStack_toSubarray(x_1);
x_3 = l_Subarray_size___redArg(x_2);
x_4 = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 2);
x_58 = lean_box(0);
x_59 = l_Lean_Syntax_isMissing(x_56);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_57);
lean_inc(x_56);
lean_dec_ref(x_4);
x_60 = l_Lean_Syntax_getRange_x3f(x_56, x_59);
if (lean_obj_tag(x_60) == 1)
{
uint8_t x_61; 
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_64);
x_44 = x_56;
x_45 = x_57;
x_46 = x_60;
x_47 = x_63;
goto block_55;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_44 = x_56;
x_45 = x_57;
x_46 = x_68;
x_47 = x_66;
goto block_55;
}
}
else
{
lean_dec(x_60);
x_44 = x_56;
x_45 = x_57;
x_46 = x_58;
x_47 = x_2;
goto block_55;
}
}
else
{
lean_dec_ref(x_3);
x_18 = x_4;
x_19 = x_58;
x_20 = x_2;
goto block_31;
}
block_17:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = 1;
x_10 = 2;
x_11 = 0;
x_12 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
x_13 = l_Lean_Parser_Error_toString(x_5);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 2, x_11);
return x_16;
}
block_31:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
lean_inc_ref(x_22);
x_23 = l_Lean_FileMap_toPosition(x_22, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_22);
x_24 = lean_box(0);
x_5 = x_18;
x_6 = x_21;
x_7 = x_23;
x_8 = x_24;
goto block_17;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = l_Lean_FileMap_toPosition(x_22, x_26);
lean_dec(x_26);
lean_ctor_set(x_19, 0, x_27);
x_5 = x_18;
x_6 = x_21;
x_7 = x_23;
x_8 = x_19;
goto block_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_FileMap_toPosition(x_22, x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_5 = x_18;
x_6 = x_21;
x_7 = x_23;
x_8 = x_30;
goto block_17;
}
}
}
block_43:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
x_38 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(x_3);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 2);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_nat_dec_eq(x_41, x_32);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_40);
x_18 = x_37;
x_19 = x_34;
x_20 = x_32;
goto block_31;
}
else
{
lean_dec(x_32);
x_18 = x_37;
x_19 = x_34;
x_20 = x_40;
goto block_31;
}
}
else
{
lean_dec(x_38);
x_18 = x_37;
x_19 = x_34;
x_20 = x_32;
goto block_31;
}
}
block_55:
{
switch (lean_obj_tag(x_44)) {
case 3:
{
lean_object* x_48; 
x_48 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1));
x_32 = x_47;
x_33 = x_44;
x_34 = x_46;
x_35 = x_45;
x_36 = x_48;
goto block_43;
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_44, 1);
x_50 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2));
x_51 = lean_string_append(x_50, x_49);
x_52 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3));
x_53 = lean_string_append(x_51, x_52);
x_32 = x_47;
x_33 = x_44;
x_34 = x_46;
x_35 = x_45;
x_36 = x_53;
goto block_43;
}
default: 
{
lean_object* x_54; 
x_54 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4));
x_32 = x_47;
x_33 = x_44;
x_34 = x_46;
x_35 = x_45;
x_36 = x_54;
goto block_43;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_Parser_instBEqError_beq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc_ref(x_1);
x_14 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_1, x_11, x_12, x_13);
x_15 = l_Lean_MessageLog_add(x_14, x_5);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_5 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_23; 
x_5 = 0;
x_23 = l_Lean_Syntax_getPos_x3f(x_3, x_5);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(0u);
x_16 = x_24;
goto block_22;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
x_16 = x_25;
goto block_22;
}
block_15:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_FileMap_toPosition(x_6, x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = 2;
x_13 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
x_14 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 2, x_5);
return x_14;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_2);
lean_inc_ref(x_18);
x_19 = l_Lean_FileMap_toPosition(x_18, x_16);
x_20 = l_Lean_Syntax_getTailPos_x3f(x_3, x_5);
if (lean_obj_tag(x_20) == 0)
{
x_6 = x_18;
x_7 = x_17;
x_8 = x_19;
x_9 = x_16;
goto block_15;
}
else
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_6 = x_18;
x_7 = x_17;
x_8 = x_19;
x_9 = x_21;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_17);
x_18 = l_Lean_Syntax_isOfKind(x_17, x_16);
if (x_18 == 0)
{
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_100; lean_object* x_101; lean_object* x_112; uint8_t x_113; 
x_69 = lean_unsigned_to_nat(0u);
x_85 = lean_unsigned_to_nat(1u);
x_112 = l_Lean_Syntax_getArg(x_17, x_69);
x_113 = l_Lean_Syntax_isNone(x_112);
if (x_113 == 0)
{
uint8_t x_114; 
lean_inc(x_112);
x_114 = l_Lean_Syntax_matchesNull(x_112, x_85);
if (x_114 == 0)
{
lean_dec(x_112);
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = l_Lean_Syntax_getArg(x_112, x_69);
lean_dec(x_112);
x_116 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
lean_inc(x_115);
x_117 = l_Lean_Syntax_isOfKind(x_115, x_116);
if (x_117 == 0)
{
lean_dec(x_115);
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_Syntax_getArg(x_115, x_69);
lean_dec(x_115);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_100 = x_119;
x_101 = lean_box(0);
goto block_111;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_112);
x_120 = lean_box(0);
x_100 = x_120;
x_101 = lean_box(0);
goto block_111;
}
block_26:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2;
lean_inc_ref(x_1);
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(x_18, x_1, x_22, x_23);
lean_dec(x_22);
x_25 = l_Lean_MessageLog_add(x_24, x_20);
x_8 = x_25;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_dec(x_19);
x_8 = x_20;
x_9 = lean_box(0);
goto block_13;
}
}
block_35:
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec_ref(x_27);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5;
lean_inc_ref(x_1);
x_33 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(x_18, x_1, x_31, x_32);
lean_dec(x_31);
x_34 = l_Lean_MessageLog_add(x_33, x_29);
x_19 = x_28;
x_20 = x_34;
x_21 = lean_box(0);
goto block_26;
}
else
{
lean_dec(x_27);
x_19 = x_28;
x_20 = x_29;
x_21 = lean_box(0);
goto block_26;
}
}
block_68:
{
if (lean_obj_tag(x_36) == 1)
{
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_37);
lean_dec_ref(x_36);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
if (x_39 == 0)
{
lean_free_object(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec_ref(x_36);
x_44 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6));
x_45 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_37, x_39);
x_46 = lean_string_append(x_44, x_45);
x_47 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7));
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_45);
lean_dec_ref(x_45);
x_50 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8));
x_51 = lean_string_append(x_49, x_50);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_51);
x_52 = l_Lean_MessageData_ofFormat(x_38);
lean_inc_ref(x_1);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(x_18, x_1, x_43, x_52);
lean_dec(x_43);
x_54 = l_Lean_MessageLog_add(x_53, x_6);
x_8 = x_54;
x_9 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec(x_38);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_36);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_36, 0);
lean_inc(x_55);
lean_dec_ref(x_36);
x_56 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6));
x_57 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_37, x_39);
x_58 = lean_string_append(x_56, x_57);
x_59 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7));
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_string_append(x_60, x_57);
lean_dec_ref(x_57);
x_62 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8));
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_MessageData_ofFormat(x_64);
lean_inc_ref(x_1);
x_66 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(x_18, x_1, x_55, x_65);
lean_dec(x_55);
x_67 = l_Lean_MessageLog_add(x_66, x_6);
x_8 = x_67;
x_9 = lean_box(0);
goto block_13;
}
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
}
block_84:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_unsigned_to_nat(5u);
x_75 = l_Lean_Syntax_getArg(x_17, x_74);
x_76 = l_Lean_Syntax_matchesNull(x_75, x_69);
if (x_76 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_unsigned_to_nat(4u);
x_78 = l_Lean_Syntax_getArg(x_17, x_77);
lean_dec(x_17);
x_79 = l_Lean_TSyntax_getId(x_78);
lean_dec(x_78);
if (lean_obj_tag(x_2) == 0)
{
if (x_76 == 0)
{
lean_dec(x_70);
x_36 = x_72;
x_37 = x_79;
x_38 = x_71;
x_39 = x_76;
x_40 = lean_box(0);
goto block_68;
}
else
{
lean_dec(x_79);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
lean_dec_ref(x_71);
x_81 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11;
lean_inc_ref(x_1);
x_82 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(x_18, x_1, x_80, x_81);
lean_dec(x_80);
x_83 = l_Lean_MessageLog_add(x_82, x_6);
x_27 = x_70;
x_28 = x_72;
x_29 = x_83;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_dec(x_71);
x_27 = x_70;
x_28 = x_72;
x_29 = x_6;
x_30 = lean_box(0);
goto block_35;
}
}
}
else
{
lean_dec(x_70);
x_36 = x_72;
x_37 = x_79;
x_38 = x_71;
x_39 = x_76;
x_40 = lean_box(0);
goto block_68;
}
}
}
block_99:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_unsigned_to_nat(3u);
x_90 = l_Lean_Syntax_getArg(x_17, x_89);
x_91 = l_Lean_Syntax_isNone(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_inc(x_90);
x_92 = l_Lean_Syntax_matchesNull(x_90, x_85);
if (x_92 == 0)
{
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = l_Lean_Syntax_getArg(x_90, x_69);
lean_dec(x_90);
x_94 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
lean_inc(x_93);
x_95 = l_Lean_Syntax_isOfKind(x_93, x_94);
if (x_95 == 0)
{
lean_dec(x_93);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_Syntax_getArg(x_93, x_69);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_70 = x_87;
x_71 = x_86;
x_72 = x_97;
x_73 = lean_box(0);
goto block_84;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_90);
x_98 = lean_box(0);
x_70 = x_87;
x_71 = x_86;
x_72 = x_98;
x_73 = lean_box(0);
goto block_84;
}
}
block_111:
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_Syntax_getArg(x_17, x_85);
x_103 = l_Lean_Syntax_isNone(x_102);
if (x_103 == 0)
{
uint8_t x_104; 
lean_inc(x_102);
x_104 = l_Lean_Syntax_matchesNull(x_102, x_85);
if (x_104 == 0)
{
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = l_Lean_Syntax_getArg(x_102, x_69);
lean_dec(x_102);
x_106 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
lean_inc(x_105);
x_107 = l_Lean_Syntax_isOfKind(x_105, x_106);
if (x_107 == 0)
{
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_17);
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Syntax_getArg(x_105, x_69);
lean_dec(x_105);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_86 = x_100;
x_87 = x_109;
x_88 = lean_box(0);
goto block_99;
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_102);
x_110 = lean_box(0);
x_86 = x_100;
x_87 = x_110;
x_88 = lean_box(0);
goto block_99;
}
}
}
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
x_5 = x_11;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(x_1, x_2, x_3, x_8, x_9, x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_parseHeader___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_parseHeader___closed__1;
x_4 = l_Lean_Parser_parseHeader___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_Parser_parseHeader___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_mk_empty_environment(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_74; uint8_t x_100; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_7 = l_Lean_Parser_Module_header;
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_9 = x_7;
} else {
 lean_dec_ref(x_7);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_11 = l_Lean_Parser_getTokenTable(x_5);
x_12 = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_8);
x_14 = l_Lean_Parser_Module_updateTokens(x_11);
x_15 = l_Lean_Options_empty;
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Lean_Parser_mkParserState(x_10);
lean_inc_ref(x_1);
x_20 = l_Lean_Parser_ParserFn_run(x_13, x_1, x_18, x_14, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 4);
lean_inc(x_23);
x_56 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Parser_SyntaxStack_isEmpty(x_21);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = l_Lean_Parser_SyntaxStack_back(x_21);
lean_dec_ref(x_21);
x_74 = x_101;
goto block_99;
}
else
{
lean_object* x_102; 
lean_dec_ref(x_21);
x_102 = lean_box(0);
x_74 = x_102;
goto block_99;
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_9)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_9;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
if (lean_is_scalar(x_6)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_6;
}
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
block_40:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(0);
x_37 = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(x_23, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = 1;
x_24 = x_34;
x_25 = x_33;
x_26 = lean_box(0);
x_27 = x_38;
goto block_32;
}
else
{
uint8_t x_39; 
x_39 = 0;
x_24 = x_34;
x_25 = x_33;
x_26 = lean_box(0);
x_27 = x_39;
goto block_32;
}
}
block_55:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; 
x_46 = lean_unsigned_to_nat(2u);
x_47 = l_Lean_Syntax_getArg(x_43, x_46);
x_48 = l_Lean_Syntax_getArgs(x_47);
lean_dec(x_47);
x_49 = lean_array_size(x_48);
x_50 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(x_1, x_44, x_48, x_49, x_41, x_42);
lean_dec_ref(x_48);
lean_dec(x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_33 = x_43;
x_34 = x_51;
x_35 = lean_box(0);
goto block_40;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
block_73:
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = l_Lean_Syntax_getArg(x_61, x_65);
x_67 = l_Lean_Syntax_isNone(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
lean_inc(x_66);
x_68 = l_Lean_Syntax_matchesNull(x_66, x_65);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_33 = x_61;
x_34 = x_58;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = l_Lean_Syntax_getArg(x_66, x_56);
lean_dec(x_66);
x_70 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
x_71 = l_Lean_Name_mkStr4(x_59, x_60, x_62, x_70);
x_72 = l_Lean_Syntax_isOfKind(x_69, x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_63);
lean_dec_ref(x_1);
x_33 = x_61;
x_34 = x_58;
x_35 = lean_box(0);
goto block_40;
}
else
{
x_41 = x_57;
x_42 = x_58;
x_43 = x_61;
x_44 = x_63;
x_45 = lean_box(0);
goto block_55;
}
}
}
else
{
lean_dec(x_66);
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
x_41 = x_57;
x_42 = x_58;
x_43 = x_61;
x_44 = x_63;
x_45 = lean_box(0);
goto block_55;
}
}
block_99:
{
lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_75 = l_Lean_Parser_parseHeader___closed__4;
x_76 = l_Lean_Parser_ParserState_allErrors(x_20);
x_77 = lean_array_size(x_76);
x_78 = 0;
lean_inc_ref(x_1);
x_79 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(x_1, x_76, x_77, x_78, x_75);
lean_dec_ref(x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__0));
x_82 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__1));
x_83 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__2));
x_84 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
lean_inc(x_74);
x_85 = l_Lean_Syntax_isOfKind(x_74, x_84);
if (x_85 == 0)
{
lean_dec_ref(x_1);
x_33 = x_74;
x_34 = x_80;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = l_Lean_Syntax_getArg(x_74, x_56);
x_87 = l_Lean_Syntax_isNone(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_unsigned_to_nat(1u);
lean_inc(x_86);
x_89 = l_Lean_Syntax_matchesNull(x_86, x_88);
if (x_89 == 0)
{
lean_dec(x_86);
lean_dec_ref(x_1);
x_33 = x_74;
x_34 = x_80;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = l_Lean_Syntax_getArg(x_86, x_56);
lean_dec(x_86);
x_91 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
lean_inc(x_90);
x_92 = l_Lean_Syntax_isOfKind(x_90, x_91);
if (x_92 == 0)
{
lean_dec(x_90);
lean_dec_ref(x_1);
x_33 = x_74;
x_34 = x_80;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_Syntax_getArg(x_90, x_56);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_57 = x_78;
x_58 = x_80;
x_59 = x_81;
x_60 = x_82;
x_61 = x_74;
x_62 = x_83;
x_63 = x_94;
x_64 = lean_box(0);
goto block_73;
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_86);
x_95 = lean_box(0);
x_57 = x_78;
x_58 = x_80;
x_59 = x_81;
x_60 = x_82;
x_61 = x_74;
x_62 = x_83;
x_63 = x_95;
x_64 = lean_box(0);
goto block_73;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_74);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_79);
if (x_96 == 0)
{
return x_79;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_79, 0);
lean_inc(x_97);
lean_dec(x_79);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_4);
if (x_103 == 0)
{
return x_4;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_4, 0);
lean_inc(x_104);
lean_dec(x_4);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_parseHeader(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
x_3 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1;
lean_inc(x_1);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
x_5 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4));
x_7 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5;
x_8 = lean_array_push(x_7, x_5);
x_9 = lean_box(2);
x_10 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
x_2 = x_9;
goto block_5;
}
else
{
x_2 = x_7;
goto block_5;
}
block_5:
{
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__4));
x_4 = l_Lean_Syntax_isOfKind(x_1, x_3);
return x_4;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isTerminalCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0;
x_8 = l_Lean_Parser_SyntaxStack_empty;
x_9 = l_Lean_Parser_initCacheForInput(x_4);
x_10 = lean_box(0);
lean_inc(x_3);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_9);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_7);
x_12 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(x_5);
x_13 = l_Lean_Parser_getTokenTable(x_5);
x_14 = l_Lean_Parser_ParserFn_run(x_12, x_1, x_2, x_13, x_11);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec_ref(x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_17 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2;
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_Module_module___closed__3;
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
x_5 = lean_apply_2(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc_ref(x_1);
x_12 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_1, x_9, x_10, x_11);
x_13 = l_Lean_MessageLog_add(x_12, x_5);
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
x_2 = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_17 = x_3;
} else {
 lean_dec_ref(x_3);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_19 = x_14;
} else {
 lean_dec_ref(x_14);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_22 = x_15;
} else {
 lean_dec_ref(x_15);
 x_22 = lean_box(0);
}
x_23 = l_Lean_Parser_InputContext_atEnd(x_1, x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; size_t x_70; size_t x_71; lean_object* x_72; uint8_t x_73; uint8_t x_92; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_1, 0);
x_26 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0;
lean_inc_ref(x_24);
x_27 = l_Lean_Parser_getTokenTable(x_24);
x_28 = l_Lean_Parser_SyntaxStack_empty;
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Parser_initCacheForInput(x_25);
x_31 = lean_box(0);
x_32 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0;
lean_inc(x_18);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_18);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set(x_33, 5, x_32);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_34 = l_Lean_Parser_ParserFn_run(x_26, x_1, x_2, x_27, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 5);
lean_inc_ref(x_38);
lean_dec_ref(x_34);
x_70 = lean_array_size(x_38);
x_71 = 0;
lean_inc_ref(x_1);
x_72 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(x_1, x_38, x_70, x_71, x_16);
lean_dec_ref(x_38);
x_92 = lean_unbox(x_20);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = lean_unbox(x_20);
x_73 = x_93;
goto block_84;
}
else
{
uint8_t x_94; 
x_94 = l_Lean_Parser_SyntaxStack_isEmpty(x_35);
if (x_94 == 0)
{
goto block_91;
}
else
{
if (x_23 == 0)
{
x_73 = x_23;
goto block_84;
}
else
{
goto block_91;
}
}
}
block_52:
{
lean_object* x_44; lean_object* x_45; 
lean_inc_ref(x_35);
lean_inc_ref(x_1);
x_44 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_1, x_36, x_35, x_42);
x_45 = l_Lean_MessageLog_add(x_44, x_43);
if (x_39 == 0)
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = 1;
x_47 = l_Lean_Parser_SyntaxStack_back(x_35);
lean_dec_ref(x_35);
x_48 = lean_box(x_46);
if (lean_is_scalar(x_22)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_22;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
if (lean_is_scalar(x_19)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_19;
}
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_17)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_17;
}
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
lean_dec_ref(x_35);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
x_4 = x_41;
x_5 = x_45;
x_6 = x_40;
goto block_13;
}
}
block_59:
{
if (x_55 == 0)
{
x_39 = x_58;
x_40 = x_53;
x_41 = x_54;
x_42 = x_56;
x_43 = x_57;
goto block_52;
}
else
{
if (x_58 == 0)
{
x_39 = x_58;
x_40 = x_53;
x_41 = x_54;
x_42 = x_56;
x_43 = x_57;
goto block_52;
}
else
{
lean_dec_ref(x_56);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
x_4 = x_54;
x_5 = x_57;
x_6 = x_53;
goto block_13;
}
}
}
block_69:
{
uint8_t x_65; 
x_65 = l_Lean_Parser_SyntaxStack_isEmpty(x_35);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Parser_SyntaxStack_back(x_35);
x_67 = l_Lean_Syntax_getPos_x3f(x_66, x_65);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = 1;
x_53 = x_64;
x_54 = x_62;
x_55 = x_63;
x_56 = x_60;
x_57 = x_61;
x_58 = x_68;
goto block_59;
}
else
{
lean_dec_ref(x_67);
x_53 = x_64;
x_54 = x_62;
x_55 = x_63;
x_56 = x_60;
x_57 = x_61;
x_58 = x_65;
goto block_59;
}
}
else
{
x_53 = x_64;
x_54 = x_62;
x_55 = x_63;
x_56 = x_60;
x_57 = x_61;
x_58 = x_65;
goto block_59;
}
}
block_84:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_74 = l_Lean_Parser_SyntaxStack_back(x_35);
lean_dec_ref(x_35);
x_75 = lean_box(x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_36);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_37, 0);
lean_inc(x_79);
lean_dec_ref(x_37);
x_80 = lean_nat_dec_eq(x_36, x_18);
lean_dec(x_18);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = lean_unbox(x_20);
lean_dec(x_20);
lean_inc(x_36);
x_60 = x_79;
x_61 = x_72;
x_62 = x_36;
x_63 = x_81;
x_64 = x_21;
goto block_69;
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_inc(x_36);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_82 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(x_1, x_2, x_36);
x_83 = lean_unbox(x_20);
lean_dec(x_20);
x_60 = x_79;
x_61 = x_72;
x_62 = x_82;
x_63 = x_83;
x_64 = x_21;
goto block_69;
}
}
}
block_91:
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Parser_SyntaxStack_back(x_35);
x_86 = l_Lean_Syntax_isAntiquot(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
x_73 = x_86;
goto block_84;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_37);
lean_dec_ref(x_35);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_20);
lean_ctor_set(x_87, 1, x_21);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_36);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_72);
lean_ctor_set(x_89, 1, x_88);
x_3 = x_89;
goto _start;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_21);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc(x_18);
x_95 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(x_18);
if (lean_is_scalar(x_22)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_22;
}
lean_ctor_set(x_96, 0, x_20);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_19)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_19;
}
lean_ctor_set(x_97, 0, x_18);
lean_ctor_set(x_97, 1, x_96);
if (lean_is_scalar(x_17)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_17;
}
lean_ctor_set(x_98, 0, x_16);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
block_13:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_8 = lean_box(0);
x_9 = lean_box(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(x_1, x_2, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_3, 0, x_18);
x_23 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_23);
lean_ctor_set(x_15, 1, x_16);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_18);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_14, 1, x_27);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_31 = x_15;
} else {
 lean_dec_ref(x_15);
 x_31 = lean_box(0);
}
lean_ctor_set(x_3, 0, x_28);
x_32 = lean_unbox(x_29);
lean_dec(x_29);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_32);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_16);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_35);
lean_dec(x_3);
x_37 = lean_box(0);
x_38 = lean_box(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(x_1, x_2, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec_ref(x_42);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_46);
x_52 = lean_unbox(x_48);
lean_dec(x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_52);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Message_toString(x_2, x_1);
x_5 = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_9 = lean_apply_2(x_1, x_8, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_7);
if (x_10 == 0)
{
if (x_9 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
lean_free_object(x_2);
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_5, x_11, x_12, x_8);
lean_dec_ref(x_5);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
lean_free_object(x_2);
x_14 = 0;
x_15 = lean_usize_of_nat(x_7);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_5, x_14, x_15, x_8);
lean_dec_ref(x_5);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_17);
x_20 = lean_box(0);
x_21 = lean_nat_dec_lt(x_18, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_19, x_19);
if (x_23 == 0)
{
if (x_21 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_19);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_17, x_25, x_26, x_20);
lean_dec_ref(x_17);
return x_27;
}
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_19);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_17, x_28, x_29, x_20);
lean_dec_ref(x_17);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_32);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_33, x_34);
if (x_36 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
if (x_36 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
lean_free_object(x_2);
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_32, x_38, x_39, x_35);
lean_dec_ref(x_32);
return x_40;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
lean_free_object(x_2);
x_41 = 0;
x_42 = lean_usize_of_nat(x_34);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_32, x_41, x_42, x_35);
lean_dec_ref(x_32);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = lean_box(0);
x_48 = lean_nat_dec_lt(x_45, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec_ref(x_44);
lean_dec_ref(x_1);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_46, x_46);
if (x_50 == 0)
{
if (x_48 == 0)
{
lean_object* x_51; 
lean_dec_ref(x_44);
lean_dec_ref(x_1);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_47);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_46);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_44, x_52, x_53, x_47);
lean_dec_ref(x_44);
return x_54;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_46);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_44, x_55, x_56, x_47);
lean_dec_ref(x_44);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_9 = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_6 = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_5);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
if (x_12 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
lean_free_object(x_6);
x_14 = 0;
x_15 = lean_usize_of_nat(x_10);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_5, x_14, x_15, x_11);
lean_dec_ref(x_5);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_6);
x_17 = 0;
x_18 = lean_usize_of_nat(x_10);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_5, x_17, x_18, x_11);
lean_dec_ref(x_5);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_5);
x_22 = lean_box(0);
x_23 = lean_nat_dec_lt(x_20, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
if (x_23 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_5, x_27, x_28, x_22);
lean_dec_ref(x_5);
return x_29;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_21);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_5, x_30, x_31, x_22);
lean_dec_ref(x_5);
return x_32;
}
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0;
x_8 = lean_usize_shift_right(x_3, x_4);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get_borrowed(x_7, x_6, x_9);
x_11 = 1;
x_12 = lean_usize_shift_left(x_11, x_4);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = 5;
x_16 = lean_usize_sub(x_4, x_15);
lean_inc(x_10);
lean_inc_ref(x_1);
x_17 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(x_1, x_10, x_14, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_9, x_20);
lean_dec(x_9);
x_22 = lean_array_get_size(x_6);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_17);
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = lean_usize_of_nat(x_22);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_6, x_26, x_27, x_23);
lean_dec_ref(x_6);
return x_28;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_free_object(x_17);
x_29 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_30 = lean_usize_of_nat(x_22);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_6, x_29, x_30, x_23);
lean_dec_ref(x_6);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_17);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_dec(x_9);
x_34 = lean_array_get_size(x_6);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_33, x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_34, x_34);
if (x_38 == 0)
{
if (x_36 == 0)
{
lean_object* x_39; 
lean_dec(x_33);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_35);
return x_39;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_41 = lean_usize_of_nat(x_34);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_6, x_40, x_41, x_35);
lean_dec_ref(x_6);
return x_42;
}
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_44 = lean_usize_of_nat(x_34);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(x_1, x_6, x_43, x_44, x_35);
lean_dec_ref(x_6);
return x_45;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_17;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_usize_to_nat(x_3);
x_49 = lean_array_get_size(x_47);
x_50 = lean_box(0);
x_51 = lean_nat_dec_lt(x_48, x_49);
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_50);
return x_2;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_49, x_49);
if (x_52 == 0)
{
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_50);
return x_2;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
lean_free_object(x_2);
x_53 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_54 = lean_usize_of_nat(x_49);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_47, x_53, x_54, x_50);
lean_dec_ref(x_47);
return x_55;
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
lean_free_object(x_2);
x_56 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_57 = lean_usize_of_nat(x_49);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_47, x_56, x_57, x_50);
lean_dec_ref(x_47);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_usize_to_nat(x_3);
x_61 = lean_array_get_size(x_59);
x_62 = lean_box(0);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_61, x_61);
if (x_65 == 0)
{
if (x_63 == 0)
{
lean_object* x_66; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_62);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_68 = lean_usize_of_nat(x_61);
x_69 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_59, x_67, x_68, x_62);
lean_dec_ref(x_59);
return x_69;
}
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; 
x_70 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_71 = lean_usize_of_nat(x_61);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_59, x_70, x_71, x_62);
lean_dec_ref(x_59);
return x_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(x_1, x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_usize(x_2, 4);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_nat_dec_le(x_10, x_3);
if (x_11 == 0)
{
size_t x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_usize_of_nat(x_3);
lean_inc_ref(x_1);
x_13 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(x_1, x_7, x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_array_get_size(x_8);
x_17 = lean_box(0);
x_18 = lean_nat_dec_lt(x_5, x_16);
if (x_18 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_16, x_16);
if (x_19 == 0)
{
if (x_18 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_free_object(x_13);
x_20 = 0;
x_21 = lean_usize_of_nat(x_16);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_8, x_20, x_21, x_17);
lean_dec_ref(x_8);
return x_22;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_13);
x_23 = 0;
x_24 = lean_usize_of_nat(x_16);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_8, x_23, x_24, x_17);
lean_dec_ref(x_8);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_13);
x_26 = lean_array_get_size(x_8);
x_27 = lean_box(0);
x_28 = lean_nat_dec_lt(x_5, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
if (x_28 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_27);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_8, x_32, x_33, x_27);
lean_dec_ref(x_8);
return x_34;
}
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_26);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_8, x_35, x_36, x_27);
lean_dec_ref(x_8);
return x_37;
}
}
}
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_13;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec_ref(x_7);
x_38 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_39 = lean_array_get_size(x_8);
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_38);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
if (x_41 == 0)
{
lean_object* x_44; 
lean_dec(x_38);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_40);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_46 = lean_usize_of_nat(x_39);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_8, x_45, x_46, x_40);
lean_dec_ref(x_8);
return x_47;
}
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_49 = lean_usize_of_nat(x_39);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(x_1, x_8, x_48, x_49, x_40);
lean_dec_ref(x_8);
return x_50;
}
}
}
}
else
{
lean_object* x_51; 
x_51 = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(x_1, x_2);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_29; 
x_7 = l_Lean_Options_empty;
x_8 = lean_box(0);
x_9 = lean_box(0);
lean_inc_ref(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_inc_ref(x_2);
x_11 = l_Lean_Parser_parseCommand(x_2, x_10, x_3, x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_13);
x_29 = l_Lean_Parser_isTerminalCommand(x_13);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_array_push(x_5, x_13);
x_3 = x_14;
x_4 = x_15;
x_5 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = l_Lean_MessageLog_hasUnreported(x_15);
if (x_32 == 0)
{
if (x_29 == 0)
{
lean_dec_ref(x_5);
x_16 = x_29;
goto block_28;
}
else
{
lean_object* x_33; 
lean_dec(x_15);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_5);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_5);
x_34 = 0;
x_16 = x_34;
goto block_28;
}
}
block_28:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(x_15, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1;
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1;
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_testParseModuleAux(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_testParseModule___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_testParseModule___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 1;
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = l_Lean_Parser_mkInputContext___redArg(x_3, x_2, x_5, x_6);
lean_inc_ref(x_7);
x_8 = l_Lean_Parser_parseHeader(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Parser_testParseModule___closed__0;
x_15 = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(x_1, x_7, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_19 = l_Lean_mkListNode(x_17);
x_20 = l_Lean_Parser_testParseModule___closed__1;
x_21 = lean_array_push(x_20, x_11);
x_22 = lean_array_push(x_21, x_19);
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_22);
x_25 = l_Lean_Syntax_updateLeading(x_24);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_28 = l_Lean_mkListNode(x_26);
x_29 = l_Lean_Parser_testParseModule___closed__1;
x_30 = lean_array_push(x_29, x_11);
x_31 = lean_array_push(x_30, x_28);
x_32 = lean_box(2);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_31);
x_34 = l_Lean_Syntax_updateLeading(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_11);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_testParseModule(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readFile(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Parser_testParseModule(x_1, x_2, x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_testParseFile(x_1, x_2);
return x_4;
}
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_moduleTk___closed__5 = _init_l_Lean_Parser_Module_moduleTk___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk___closed__5);
l_Lean_Parser_Module_moduleTk___closed__7 = _init_l_Lean_Parser_Module_moduleTk___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk___closed__7);
l_Lean_Parser_Module_moduleTk___closed__8 = _init_l_Lean_Parser_Module_moduleTk___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk___closed__8);
l_Lean_Parser_Module_moduleTk___closed__9 = _init_l_Lean_Parser_Module_moduleTk___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk___closed__9);
l_Lean_Parser_Module_moduleTk___closed__10 = _init_l_Lean_Parser_Module_moduleTk___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk___closed__10);
l_Lean_Parser_Module_moduleTk = _init_l_Lean_Parser_Module_moduleTk();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk);
l_Lean_Parser_Module_prelude___closed__2 = _init_l_Lean_Parser_Module_prelude___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__2);
l_Lean_Parser_Module_prelude___closed__3 = _init_l_Lean_Parser_Module_prelude___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__3);
l_Lean_Parser_Module_prelude___closed__4 = _init_l_Lean_Parser_Module_prelude___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__4);
l_Lean_Parser_Module_prelude___closed__5 = _init_l_Lean_Parser_Module_prelude___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__5);
l_Lean_Parser_Module_prelude___closed__6 = _init_l_Lean_Parser_Module_prelude___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__6);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean_mark_persistent(l_Lean_Parser_Module_prelude);
l_Lean_Parser_Module_public___closed__2 = _init_l_Lean_Parser_Module_public___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_public___closed__2);
l_Lean_Parser_Module_public___closed__3 = _init_l_Lean_Parser_Module_public___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_public___closed__3);
l_Lean_Parser_Module_public___closed__4 = _init_l_Lean_Parser_Module_public___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_public___closed__4);
l_Lean_Parser_Module_public___closed__5 = _init_l_Lean_Parser_Module_public___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_public___closed__5);
l_Lean_Parser_Module_public___closed__6 = _init_l_Lean_Parser_Module_public___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_public___closed__6);
l_Lean_Parser_Module_public = _init_l_Lean_Parser_Module_public();
lean_mark_persistent(l_Lean_Parser_Module_public);
l_Lean_Parser_Module_meta___closed__2 = _init_l_Lean_Parser_Module_meta___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_meta___closed__2);
l_Lean_Parser_Module_meta___closed__3 = _init_l_Lean_Parser_Module_meta___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_meta___closed__3);
l_Lean_Parser_Module_meta___closed__4 = _init_l_Lean_Parser_Module_meta___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_meta___closed__4);
l_Lean_Parser_Module_meta___closed__5 = _init_l_Lean_Parser_Module_meta___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_meta___closed__5);
l_Lean_Parser_Module_meta___closed__6 = _init_l_Lean_Parser_Module_meta___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_meta___closed__6);
l_Lean_Parser_Module_meta = _init_l_Lean_Parser_Module_meta();
lean_mark_persistent(l_Lean_Parser_Module_meta);
l_Lean_Parser_Module_all___closed__2 = _init_l_Lean_Parser_Module_all___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_all___closed__2);
l_Lean_Parser_Module_all___closed__3 = _init_l_Lean_Parser_Module_all___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_all___closed__3);
l_Lean_Parser_Module_all___closed__4 = _init_l_Lean_Parser_Module_all___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_all___closed__4);
l_Lean_Parser_Module_all___closed__5 = _init_l_Lean_Parser_Module_all___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_all___closed__5);
l_Lean_Parser_Module_all___closed__6 = _init_l_Lean_Parser_Module_all___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_all___closed__6);
l_Lean_Parser_Module_all = _init_l_Lean_Parser_Module_all();
lean_mark_persistent(l_Lean_Parser_Module_all);
l_Lean_Parser_Module_import___closed__2 = _init_l_Lean_Parser_Module_import___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__2);
l_Lean_Parser_Module_import___closed__3 = _init_l_Lean_Parser_Module_import___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__3);
l_Lean_Parser_Module_import___closed__4 = _init_l_Lean_Parser_Module_import___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__4);
l_Lean_Parser_Module_import___closed__6 = _init_l_Lean_Parser_Module_import___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__6);
l_Lean_Parser_Module_import___closed__7 = _init_l_Lean_Parser_Module_import___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__7);
l_Lean_Parser_Module_import___closed__8 = _init_l_Lean_Parser_Module_import___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__8);
l_Lean_Parser_Module_import___closed__9 = _init_l_Lean_Parser_Module_import___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__9);
l_Lean_Parser_Module_import___closed__10 = _init_l_Lean_Parser_Module_import___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__10);
l_Lean_Parser_Module_import___closed__11 = _init_l_Lean_Parser_Module_import___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__11);
l_Lean_Parser_Module_import___closed__12 = _init_l_Lean_Parser_Module_import___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__12);
l_Lean_Parser_Module_import___closed__13 = _init_l_Lean_Parser_Module_import___closed__13();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__13);
l_Lean_Parser_Module_import___closed__14 = _init_l_Lean_Parser_Module_import___closed__14();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__14);
l_Lean_Parser_Module_import___closed__15 = _init_l_Lean_Parser_Module_import___closed__15();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__15);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean_mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header___closed__2 = _init_l_Lean_Parser_Module_header___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__2);
l_Lean_Parser_Module_header___closed__3 = _init_l_Lean_Parser_Module_header___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__3);
l_Lean_Parser_Module_header___closed__4 = _init_l_Lean_Parser_Module_header___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__4);
l_Lean_Parser_Module_header___closed__5 = _init_l_Lean_Parser_Module_header___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__5);
l_Lean_Parser_Module_header___closed__6 = _init_l_Lean_Parser_Module_header___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__6);
l_Lean_Parser_Module_header___closed__7 = _init_l_Lean_Parser_Module_header___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__7);
l_Lean_Parser_Module_header___closed__8 = _init_l_Lean_Parser_Module_header___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__8);
l_Lean_Parser_Module_header___closed__9 = _init_l_Lean_Parser_Module_header___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__9);
l_Lean_Parser_Module_header___closed__10 = _init_l_Lean_Parser_Module_header___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__10);
l_Lean_Parser_Module_header___closed__11 = _init_l_Lean_Parser_Module_header___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__11);
l_Lean_Parser_Module_header___closed__12 = _init_l_Lean_Parser_Module_header___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__12);
l_Lean_Parser_Module_header___closed__13 = _init_l_Lean_Parser_Module_header___closed__13();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__13);
l_Lean_Parser_Module_header___closed__14 = _init_l_Lean_Parser_Module_header___closed__14();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__14);
l_Lean_Parser_Module_header___closed__15 = _init_l_Lean_Parser_Module_header___closed__15();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__15);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean_mark_persistent(l_Lean_Parser_Module_header);
l_Lean_Parser_Module_moduleTk_formatter___closed__0 = _init_l_Lean_Parser_Module_moduleTk_formatter___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk_formatter___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_prelude_formatter___closed__0 = _init_l_Lean_Parser_Module_prelude_formatter___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_prelude_formatter___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_public_formatter___closed__0 = _init_l_Lean_Parser_Module_public_formatter___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_public_formatter___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_meta_formatter___closed__0 = _init_l_Lean_Parser_Module_meta_formatter___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_meta_formatter___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_all_formatter___closed__0 = _init_l_Lean_Parser_Module_all_formatter___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_all_formatter___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_import_formatter___closed__0 = _init_l_Lean_Parser_Module_import_formatter___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__0);
l_Lean_Parser_Module_import_formatter___closed__1 = _init_l_Lean_Parser_Module_import_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__1);
l_Lean_Parser_Module_import_formatter___closed__2 = _init_l_Lean_Parser_Module_import_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__2);
l_Lean_Parser_Module_import_formatter___closed__4 = _init_l_Lean_Parser_Module_import_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__4);
l_Lean_Parser_Module_import_formatter___closed__5 = _init_l_Lean_Parser_Module_import_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__5);
l_Lean_Parser_Module_import_formatter___closed__6 = _init_l_Lean_Parser_Module_import_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__6);
l_Lean_Parser_Module_import_formatter___closed__7 = _init_l_Lean_Parser_Module_import_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__7);
l_Lean_Parser_Module_import_formatter___closed__9 = _init_l_Lean_Parser_Module_import_formatter___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__9);
l_Lean_Parser_Module_import_formatter___closed__10 = _init_l_Lean_Parser_Module_import_formatter___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__10);
l_Lean_Parser_Module_import_formatter___closed__11 = _init_l_Lean_Parser_Module_import_formatter___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_import_formatter___closed__11);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_header_formatter___closed__0 = _init_l_Lean_Parser_Module_header_formatter___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__0);
l_Lean_Parser_Module_header_formatter___closed__1 = _init_l_Lean_Parser_Module_header_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__1);
l_Lean_Parser_Module_header_formatter___closed__2 = _init_l_Lean_Parser_Module_header_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__2);
l_Lean_Parser_Module_header_formatter___closed__3 = _init_l_Lean_Parser_Module_header_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__3);
l_Lean_Parser_Module_header_formatter___closed__4 = _init_l_Lean_Parser_Module_header_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__4);
l_Lean_Parser_Module_header_formatter___closed__5 = _init_l_Lean_Parser_Module_header_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__5);
l_Lean_Parser_Module_header_formatter___closed__6 = _init_l_Lean_Parser_Module_header_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__6);
l_Lean_Parser_Module_header_formatter___closed__7 = _init_l_Lean_Parser_Module_header_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__7);
l_Lean_Parser_Module_header_formatter___closed__8 = _init_l_Lean_Parser_Module_header_formatter___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__8);
l_Lean_Parser_Module_header_formatter___closed__9 = _init_l_Lean_Parser_Module_header_formatter___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__9);
l_Lean_Parser_Module_header_formatter___closed__10 = _init_l_Lean_Parser_Module_header_formatter___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__10);
l_Lean_Parser_Module_header_formatter___closed__11 = _init_l_Lean_Parser_Module_header_formatter___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_header_formatter___closed__11);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_module_formatter___closed__1 = _init_l_Lean_Parser_Module_module_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__1);
l_Lean_Parser_Module_module_formatter___closed__3 = _init_l_Lean_Parser_Module_module_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__3);
l_Lean_Parser_Module_module_formatter___closed__4 = _init_l_Lean_Parser_Module_module_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__4);
l_Lean_Parser_Module_module_formatter___closed__5 = _init_l_Lean_Parser_Module_module_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__5);
l_Lean_Parser_Module_module_formatter___closed__6 = _init_l_Lean_Parser_Module_module_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_module_formatter___closed__6);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_prelude_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_prelude_parenthesizer___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_public_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_public_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_public_parenthesizer___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_meta_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_meta_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_meta_parenthesizer___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_all_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_all_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_all_parenthesizer___closed__0);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_import_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__0);
l_Lean_Parser_Module_import_parenthesizer___closed__1 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__1);
l_Lean_Parser_Module_import_parenthesizer___closed__2 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__2);
l_Lean_Parser_Module_import_parenthesizer___closed__4 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__4);
l_Lean_Parser_Module_import_parenthesizer___closed__5 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__5);
l_Lean_Parser_Module_import_parenthesizer___closed__6 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__6);
l_Lean_Parser_Module_import_parenthesizer___closed__8 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__8);
l_Lean_Parser_Module_import_parenthesizer___closed__9 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__9);
l_Lean_Parser_Module_import_parenthesizer___closed__10 = _init_l_Lean_Parser_Module_import_parenthesizer___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_import_parenthesizer___closed__10);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_header_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__0);
l_Lean_Parser_Module_header_parenthesizer___closed__2 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__2);
l_Lean_Parser_Module_header_parenthesizer___closed__3 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__3);
l_Lean_Parser_Module_header_parenthesizer___closed__4 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__4);
l_Lean_Parser_Module_header_parenthesizer___closed__5 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__5);
l_Lean_Parser_Module_header_parenthesizer___closed__6 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__6);
l_Lean_Parser_Module_header_parenthesizer___closed__7 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__7);
l_Lean_Parser_Module_header_parenthesizer___closed__8 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__8);
l_Lean_Parser_Module_header_parenthesizer___closed__9 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__9);
l_Lean_Parser_Module_header_parenthesizer___closed__10 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__10);
l_Lean_Parser_Module_header_parenthesizer___closed__11 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__11);
l_Lean_Parser_Module_header_parenthesizer___closed__12 = _init_l_Lean_Parser_Module_header_parenthesizer___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_header_parenthesizer___closed__12);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_module_parenthesizer___closed__0 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__0);
l_Lean_Parser_Module_module_parenthesizer___closed__2 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__2);
l_Lean_Parser_Module_module_parenthesizer___closed__3 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__3);
l_Lean_Parser_Module_module_parenthesizer___closed__4 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__4);
l_Lean_Parser_Module_module_parenthesizer___closed__5 = _init_l_Lean_Parser_Module_module_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_module_parenthesizer___closed__5);
if (builtin) {res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_module___closed__0 = _init_l_Lean_Parser_Module_module___closed__0();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__0);
l_Lean_Parser_Module_module___closed__3 = _init_l_Lean_Parser_Module_module___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__3);
l_Lean_Parser_Module_module___closed__4 = _init_l_Lean_Parser_Module_module___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__4);
l_Lean_Parser_Module_module___closed__5 = _init_l_Lean_Parser_Module_module___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__5);
l_Lean_Parser_Module_module___closed__6 = _init_l_Lean_Parser_Module_module___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__6);
l_Lean_Parser_Module_module___closed__7 = _init_l_Lean_Parser_Module_module___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__7);
l_Lean_Parser_Module_module___closed__8 = _init_l_Lean_Parser_Module_module___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__8);
l_Lean_Parser_Module_module___closed__9 = _init_l_Lean_Parser_Module_module___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_module___closed__9);
l_Lean_Parser_Module_module = _init_l_Lean_Parser_Module_module();
lean_mark_persistent(l_Lean_Parser_Module_module);
l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0 = _init_l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0);
l_Lean_Parser_Module_updateTokens___closed__3 = _init_l_Lean_Parser_Module_updateTokens___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_updateTokens___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11);
l_Lean_Parser_parseHeader___closed__1 = _init_l_Lean_Parser_parseHeader___closed__1();
lean_mark_persistent(l_Lean_Parser_parseHeader___closed__1);
l_Lean_Parser_parseHeader___closed__2 = _init_l_Lean_Parser_parseHeader___closed__2();
lean_mark_persistent(l_Lean_Parser_parseHeader___closed__2);
l_Lean_Parser_parseHeader___closed__3 = _init_l_Lean_Parser_parseHeader___closed__3();
lean_mark_persistent(l_Lean_Parser_parseHeader___closed__3);
l_Lean_Parser_parseHeader___closed__4 = _init_l_Lean_Parser_parseHeader___closed__4();
lean_mark_persistent(l_Lean_Parser_parseHeader___closed__4);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1);
l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__5);
l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0);
l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1 = _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
l_Lean_Parser_testParseModule___closed__0 = _init_l_Lean_Parser_testParseModule___closed__0();
lean_mark_persistent(l_Lean_Parser_testParseModule___closed__0);
l_Lean_Parser_testParseModule___closed__1 = _init_l_Lean_Parser_testParseModule___closed__1();
lean_mark_persistent(l_Lean_Parser_testParseModule___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
