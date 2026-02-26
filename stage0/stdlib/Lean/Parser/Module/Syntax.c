// Lean compiler output
// Module: Lean.Parser.Module.Syntax
// Imports: public import Lean.Parser.Command
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
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__5;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__6 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value;
lean_object* l_Lean_Parser_symbol(lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__7;
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__8;
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__9;
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk;
static const lean_string_object l_Lean_Parser_Module_prelude___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_Parser_Module_prelude___closed__0 = (const lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l_Lean_Parser_Module_prelude___closed__1 = (const lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude;
static const lean_string_object l_Lean_Parser_Module_public___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Parser_Module_public___closed__0 = (const lean_object*)&l_Lean_Parser_Module_public___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l_Lean_Parser_Module_public___closed__1 = (const lean_object*)&l_Lean_Parser_Module_public___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public;
static const lean_string_object l_Lean_Parser_Module_meta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Parser_Module_meta___closed__0 = (const lean_object*)&l_Lean_Parser_Module_meta___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l_Lean_Parser_Module_meta___closed__1 = (const lean_object*)&l_Lean_Parser_Module_meta___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta;
static const lean_string_object l_Lean_Parser_Module_all___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Parser_Module_all___closed__0 = (const lean_object*)&l_Lean_Parser_Module_all___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l_Lean_Parser_Module_all___closed__1 = (const lean_object*)&l_Lean_Parser_Module_all___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all;
static const lean_string_object l_Lean_Parser_Module_import___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_Lean_Parser_Module_import___closed__0 = (const lean_object*)&l_Lean_Parser_Module_import___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l_Lean_Parser_Module_import___closed__1 = (const lean_object*)&l_Lean_Parser_Module_import___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__2;
lean_object* l_Lean_Parser_optional(lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__4;
static const lean_string_object l_Lean_Parser_Module_import___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l_Lean_Parser_Module_import___closed__5 = (const lean_object*)&l_Lean_Parser_Module_import___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__6;
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__8;
lean_object* l_Lean_Parser_atomic(lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__10;
extern lean_object* l_Lean_Parser_identWithPartialTrailingDot;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__11;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__12;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__13;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__14;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import;
static const lean_string_object l_Lean_Parser_Module_header___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Parser_Module_header___closed__0 = (const lean_object*)&l_Lean_Parser_Module_header___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Parser_Module_header___closed__1 = (const lean_object*)&l_Lean_Parser_Module_header___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__2;
extern lean_object* l_Lean_Parser_skip;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__8;
lean_object* l_Lean_Parser_many(lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_header___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__11;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__12;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__13;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__14;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_moduleTk_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_prelude_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_public_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_meta_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_all_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__0;
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__2;
static const lean_closure_object l_Lean_Parser_Module_import_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__5_value)} };
static const lean_object* l_Lean_Parser_Module_import_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Module_import_formatter___closed__3_value;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__5;
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__7;
lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_import_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_import_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Module_import_formatter___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__0;
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__6;
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__1;
lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_module_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_commandParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_module_formatter___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_prelude_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_public_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_meta_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_all_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__0;
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__2;
static const lean_closure_object l_Lean_Parser_Module_import_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__5_value)} };
static const lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Module_import_parenthesizer___closed__3_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__6;
lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_import_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Module_import_parenthesizer___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__0;
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_header_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppLine_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__7;
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__11;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_module_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__0;
lean_object* l_Lean_Parser_commandParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_module_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_commandParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_module_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_module_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_module_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_module_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lean_Parser_Module_module___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__0;
static const lean_string_object l_Lean_Parser_Module_module___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Parser_Module_module___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_module___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Parser_Module_module___closed__2 = (const lean_object*)&l_Lean_Parser_Module_module___closed__2_value;
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_module___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module;
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__5(void) {
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
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__7, &l_Lean_Parser_Module_moduleTk___closed__7_once, _init_l_Lean_Parser_Module_moduleTk___closed__7);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__8, &l_Lean_Parser_Module_moduleTk___closed__8_once, _init_l_Lean_Parser_Module_moduleTk___closed__8);
x_2 = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__5, &l_Lean_Parser_Module_moduleTk___closed__5_once, _init_l_Lean_Parser_Module_moduleTk___closed__5);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__9, &l_Lean_Parser_Module_moduleTk___closed__9_once, _init_l_Lean_Parser_Module_moduleTk___closed__9);
x_2 = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__10, &l_Lean_Parser_Module_moduleTk___closed__10_once, _init_l_Lean_Parser_Module_moduleTk___closed__10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__2(void) {
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
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__3, &l_Lean_Parser_Module_prelude___closed__3_once, _init_l_Lean_Parser_Module_prelude___closed__3);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__4, &l_Lean_Parser_Module_prelude___closed__4_once, _init_l_Lean_Parser_Module_prelude___closed__4);
x_2 = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__2, &l_Lean_Parser_Module_prelude___closed__2_once, _init_l_Lean_Parser_Module_prelude___closed__2);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__5, &l_Lean_Parser_Module_prelude___closed__5_once, _init_l_Lean_Parser_Module_prelude___closed__5);
x_2 = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__6, &l_Lean_Parser_Module_prelude___closed__6_once, _init_l_Lean_Parser_Module_prelude___closed__6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__2(void) {
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
static lean_object* _init_l_Lean_Parser_Module_public___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_public___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_public___closed__3, &l_Lean_Parser_Module_public___closed__3_once, _init_l_Lean_Parser_Module_public___closed__3);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_public___closed__4, &l_Lean_Parser_Module_public___closed__4_once, _init_l_Lean_Parser_Module_public___closed__4);
x_2 = lean_obj_once(&l_Lean_Parser_Module_public___closed__2, &l_Lean_Parser_Module_public___closed__2_once, _init_l_Lean_Parser_Module_public___closed__2);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_public___closed__5, &l_Lean_Parser_Module_public___closed__5_once, _init_l_Lean_Parser_Module_public___closed__5);
x_2 = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_public(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_public___closed__6, &l_Lean_Parser_Module_public___closed__6_once, _init_l_Lean_Parser_Module_public___closed__6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__2(void) {
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
static lean_object* _init_l_Lean_Parser_Module_meta___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_meta___closed__3, &l_Lean_Parser_Module_meta___closed__3_once, _init_l_Lean_Parser_Module_meta___closed__3);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_meta___closed__4, &l_Lean_Parser_Module_meta___closed__4_once, _init_l_Lean_Parser_Module_meta___closed__4);
x_2 = lean_obj_once(&l_Lean_Parser_Module_meta___closed__2, &l_Lean_Parser_Module_meta___closed__2_once, _init_l_Lean_Parser_Module_meta___closed__2);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_meta___closed__5, &l_Lean_Parser_Module_meta___closed__5_once, _init_l_Lean_Parser_Module_meta___closed__5);
x_2 = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_meta___closed__6, &l_Lean_Parser_Module_meta___closed__6_once, _init_l_Lean_Parser_Module_meta___closed__6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__2(void) {
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
static lean_object* _init_l_Lean_Parser_Module_all___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_all___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_all___closed__3, &l_Lean_Parser_Module_all___closed__3_once, _init_l_Lean_Parser_Module_all___closed__3);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_all___closed__4, &l_Lean_Parser_Module_all___closed__4_once, _init_l_Lean_Parser_Module_all___closed__4);
x_2 = lean_obj_once(&l_Lean_Parser_Module_all___closed__2, &l_Lean_Parser_Module_all___closed__2_once, _init_l_Lean_Parser_Module_all___closed__2);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_all___closed__5, &l_Lean_Parser_Module_all___closed__5_once, _init_l_Lean_Parser_Module_all___closed__5);
x_2 = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_all(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_all___closed__6, &l_Lean_Parser_Module_all___closed__6_once, _init_l_Lean_Parser_Module_all___closed__6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__2(void) {
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
static lean_object* _init_l_Lean_Parser_Module_import___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_public;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_meta;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import___closed__5));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__6, &l_Lean_Parser_Module_import___closed__6_once, _init_l_Lean_Parser_Module_import___closed__6);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import___closed__4, &l_Lean_Parser_Module_import___closed__4_once, _init_l_Lean_Parser_Module_import___closed__4);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__7, &l_Lean_Parser_Module_import___closed__7_once, _init_l_Lean_Parser_Module_import___closed__7);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import___closed__3, &l_Lean_Parser_Module_import___closed__3_once, _init_l_Lean_Parser_Module_import___closed__3);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__8, &l_Lean_Parser_Module_import___closed__8_once, _init_l_Lean_Parser_Module_import___closed__8);
x_2 = l_Lean_Parser_atomic(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_all;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot;
x_2 = lean_obj_once(&l_Lean_Parser_Module_import___closed__10, &l_Lean_Parser_Module_import___closed__10_once, _init_l_Lean_Parser_Module_import___closed__10);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__11, &l_Lean_Parser_Module_import___closed__11_once, _init_l_Lean_Parser_Module_import___closed__11);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import___closed__9, &l_Lean_Parser_Module_import___closed__9_once, _init_l_Lean_Parser_Module_import___closed__9);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__12, &l_Lean_Parser_Module_import___closed__12_once, _init_l_Lean_Parser_Module_import___closed__12);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__13, &l_Lean_Parser_Module_import___closed__13_once, _init_l_Lean_Parser_Module_import___closed__13);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import___closed__2, &l_Lean_Parser_Module_import___closed__2_once, _init_l_Lean_Parser_Module_import___closed__2);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__14, &l_Lean_Parser_Module_import___closed__14_once, _init_l_Lean_Parser_Module_import___closed__14);
x_2 = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import___closed__15, &l_Lean_Parser_Module_import___closed__15_once, _init_l_Lean_Parser_Module_import___closed__15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__2(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_skip;
x_2 = l_Lean_Parser_andthen(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__3, &l_Lean_Parser_Module_header___closed__3_once, _init_l_Lean_Parser_Module_header___closed__3);
x_2 = l_Lean_Parser_Module_moduleTk;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__4, &l_Lean_Parser_Module_header___closed__4_once, _init_l_Lean_Parser_Module_header___closed__4);
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_skip;
x_2 = l_Lean_Parser_Module_prelude;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__6, &l_Lean_Parser_Module_header___closed__6_once, _init_l_Lean_Parser_Module_header___closed__6);
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_skip;
x_2 = l_Lean_Parser_Module_import;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__8, &l_Lean_Parser_Module_header___closed__8_once, _init_l_Lean_Parser_Module_header___closed__8);
x_2 = l_Lean_Parser_many(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_skip;
x_2 = lean_obj_once(&l_Lean_Parser_Module_header___closed__9, &l_Lean_Parser_Module_header___closed__9_once, _init_l_Lean_Parser_Module_header___closed__9);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__10, &l_Lean_Parser_Module_header___closed__10_once, _init_l_Lean_Parser_Module_header___closed__10);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header___closed__7, &l_Lean_Parser_Module_header___closed__7_once, _init_l_Lean_Parser_Module_header___closed__7);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__11, &l_Lean_Parser_Module_header___closed__11_once, _init_l_Lean_Parser_Module_header___closed__11);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header___closed__5, &l_Lean_Parser_Module_header___closed__5_once, _init_l_Lean_Parser_Module_header___closed__5);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__12, &l_Lean_Parser_Module_header___closed__12_once, _init_l_Lean_Parser_Module_header___closed__12);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__13, &l_Lean_Parser_Module_header___closed__13_once, _init_l_Lean_Parser_Module_header___closed__13);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header___closed__2, &l_Lean_Parser_Module_header___closed__2_once, _init_l_Lean_Parser_Module_header___closed__2);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__14, &l_Lean_Parser_Module_header___closed__14_once, _init_l_Lean_Parser_Module_header___closed__14);
x_2 = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__15, &l_Lean_Parser_Module_header___closed__15_once, _init_l_Lean_Parser_Module_header___closed__15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk_formatter___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_moduleTk_formatter___closed__0, &l_Lean_Parser_Module_moduleTk_formatter___closed__0_once, _init_l_Lean_Parser_Module_moduleTk_formatter___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_prelude_formatter___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_prelude_formatter___closed__0, &l_Lean_Parser_Module_prelude_formatter___closed__0_once, _init_l_Lean_Parser_Module_prelude_formatter___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_public_formatter___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_public_formatter___closed__0, &l_Lean_Parser_Module_public_formatter___closed__0_once, _init_l_Lean_Parser_Module_public_formatter___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_meta_formatter___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_meta_formatter___closed__0, &l_Lean_Parser_Module_meta_formatter___closed__0_once, _init_l_Lean_Parser_Module_meta_formatter___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_all_formatter___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_all_formatter___closed__0, &l_Lean_Parser_Module_all_formatter___closed__0_once, _init_l_Lean_Parser_Module_all_formatter___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__0(void) {
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
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__3));
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__2, &l_Lean_Parser_Module_import_formatter___closed__2_once, _init_l_Lean_Parser_Module_import_formatter___closed__2);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__4, &l_Lean_Parser_Module_import_formatter___closed__4_once, _init_l_Lean_Parser_Module_import_formatter___closed__4);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__1, &l_Lean_Parser_Module_import_formatter___closed__1_once, _init_l_Lean_Parser_Module_import_formatter___closed__1);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__5, &l_Lean_Parser_Module_import_formatter___closed__5_once, _init_l_Lean_Parser_Module_import_formatter___closed__5);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__8));
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__7, &l_Lean_Parser_Module_import_formatter___closed__7_once, _init_l_Lean_Parser_Module_import_formatter___closed__7);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__9, &l_Lean_Parser_Module_import_formatter___closed__9_once, _init_l_Lean_Parser_Module_import_formatter___closed__9);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__6, &l_Lean_Parser_Module_import_formatter___closed__6_once, _init_l_Lean_Parser_Module_import_formatter___closed__6);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__10, &l_Lean_Parser_Module_import_formatter___closed__10_once, _init_l_Lean_Parser_Module_import_formatter___closed__10);
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__0, &l_Lean_Parser_Module_import_formatter___closed__0_once, _init_l_Lean_Parser_Module_import_formatter___closed__0);
x_7 = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__11, &l_Lean_Parser_Module_import_formatter___closed__11_once, _init_l_Lean_Parser_Module_import_formatter___closed__11);
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
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__0(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__1(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__1, &l_Lean_Parser_Module_header_formatter___closed__1_once, _init_l_Lean_Parser_Module_header_formatter___closed__1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__2, &l_Lean_Parser_Module_header_formatter___closed__2_once, _init_l_Lean_Parser_Module_header_formatter___closed__2);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__4(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__4, &l_Lean_Parser_Module_header_formatter___closed__4_once, _init_l_Lean_Parser_Module_header_formatter___closed__4);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__6(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__6, &l_Lean_Parser_Module_header_formatter___closed__6_once, _init_l_Lean_Parser_Module_header_formatter___closed__6);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__7, &l_Lean_Parser_Module_header_formatter___closed__7_once, _init_l_Lean_Parser_Module_header_formatter___closed__7);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__8, &l_Lean_Parser_Module_header_formatter___closed__8_once, _init_l_Lean_Parser_Module_header_formatter___closed__8);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__5, &l_Lean_Parser_Module_header_formatter___closed__5_once, _init_l_Lean_Parser_Module_header_formatter___closed__5);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__9, &l_Lean_Parser_Module_header_formatter___closed__9_once, _init_l_Lean_Parser_Module_header_formatter___closed__9);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__3, &l_Lean_Parser_Module_header_formatter___closed__3_once, _init_l_Lean_Parser_Module_header_formatter___closed__3);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__10, &l_Lean_Parser_Module_header_formatter___closed__10_once, _init_l_Lean_Parser_Module_header_formatter___closed__10);
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__0, &l_Lean_Parser_Module_header_formatter___closed__0_once, _init_l_Lean_Parser_Module_header_formatter___closed__0);
x_7 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__11, &l_Lean_Parser_Module_header_formatter___closed__11_once, _init_l_Lean_Parser_Module_header_formatter___closed__11);
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
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__1(void) {
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
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__1, &l_Lean_Parser_Module_header_formatter___closed__1_once, _init_l_Lean_Parser_Module_header_formatter___closed__1);
x_2 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__3, &l_Lean_Parser_Module_module_formatter___closed__3_once, _init_l_Lean_Parser_Module_module_formatter___closed__3);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__4, &l_Lean_Parser_Module_module_formatter___closed__4_once, _init_l_Lean_Parser_Module_module_formatter___closed__4);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__5, &l_Lean_Parser_Module_module_formatter___closed__5_once, _init_l_Lean_Parser_Module_module_formatter___closed__5);
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__1, &l_Lean_Parser_Module_module_formatter___closed__1_once, _init_l_Lean_Parser_Module_module_formatter___closed__1);
x_7 = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__6, &l_Lean_Parser_Module_module_formatter___closed__6_once, _init_l_Lean_Parser_Module_module_formatter___closed__6);
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
static lean_object* _init_l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0, &l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_prelude_parenthesizer___closed__0, &l_Lean_Parser_Module_prelude_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_prelude_parenthesizer___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_public_parenthesizer___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_public_parenthesizer___closed__0, &l_Lean_Parser_Module_public_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_public_parenthesizer___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_meta_parenthesizer___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_meta_parenthesizer___closed__0, &l_Lean_Parser_Module_meta_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_meta_parenthesizer___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_all_parenthesizer___closed__0(void) {
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_all_parenthesizer___closed__0, &l_Lean_Parser_Module_all_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_all_parenthesizer___closed__0);
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
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__0(void) {
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
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_parenthesizer___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_parenthesizer___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__3));
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__2, &l_Lean_Parser_Module_import_parenthesizer___closed__2_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__2);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__4, &l_Lean_Parser_Module_import_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__4);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__1, &l_Lean_Parser_Module_import_parenthesizer___closed__1_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__7));
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__6, &l_Lean_Parser_Module_import_parenthesizer___closed__6_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__6);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__8, &l_Lean_Parser_Module_import_parenthesizer___closed__8_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__8);
x_2 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__5, &l_Lean_Parser_Module_import_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__5);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__9, &l_Lean_Parser_Module_import_parenthesizer___closed__9_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__9);
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__0, &l_Lean_Parser_Module_import_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__0);
x_7 = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__10, &l_Lean_Parser_Module_import_parenthesizer___closed__10_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__10);
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
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__0(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__2(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__2, &l_Lean_Parser_Module_header_parenthesizer___closed__2_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__2);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__3, &l_Lean_Parser_Module_header_parenthesizer___closed__3_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__3);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__5(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__5, &l_Lean_Parser_Module_header_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__5);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__7(void) {
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
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__7, &l_Lean_Parser_Module_header_parenthesizer___closed__7_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__7);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
x_2 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__8, &l_Lean_Parser_Module_header_parenthesizer___closed__8_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__8);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__9, &l_Lean_Parser_Module_header_parenthesizer___closed__9_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__9);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__6, &l_Lean_Parser_Module_header_parenthesizer___closed__6_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__6);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__10, &l_Lean_Parser_Module_header_parenthesizer___closed__10_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__10);
x_2 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__4, &l_Lean_Parser_Module_header_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__4);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__11, &l_Lean_Parser_Module_header_parenthesizer___closed__11_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__11);
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__0, &l_Lean_Parser_Module_header_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__0);
x_7 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__12, &l_Lean_Parser_Module_header_parenthesizer___closed__12_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__12);
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
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__0(void) {
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
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__2, &l_Lean_Parser_Module_header_parenthesizer___closed__2_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__2);
x_2 = ((lean_object*)(l_Lean_Parser_Module_module_parenthesizer___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__2, &l_Lean_Parser_Module_module_parenthesizer___closed__2_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__2);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__3, &l_Lean_Parser_Module_module_parenthesizer___closed__3_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__3);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__4, &l_Lean_Parser_Module_module_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__4);
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
x_6 = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__0, &l_Lean_Parser_Module_module_parenthesizer___closed__0_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__0);
x_7 = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__5, &l_Lean_Parser_Module_module_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__5);
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
static lean_object* _init_l_Lean_Parser_Module_module___closed__0(void) {
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
static lean_object* _init_l_Lean_Parser_Module_module___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Parser_Module_module___closed__2));
x_3 = l_Lean_Parser_categoryParser(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_header___closed__3, &l_Lean_Parser_Module_header___closed__3_once, _init_l_Lean_Parser_Module_header___closed__3);
x_2 = lean_obj_once(&l_Lean_Parser_Module_module___closed__3, &l_Lean_Parser_Module_module___closed__3_once, _init_l_Lean_Parser_Module_module___closed__3);
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module___closed__4, &l_Lean_Parser_Module_module___closed__4_once, _init_l_Lean_Parser_Module_module___closed__4);
x_2 = l_Lean_Parser_many(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module___closed__5, &l_Lean_Parser_Module_module___closed__5_once, _init_l_Lean_Parser_Module_module___closed__5);
x_2 = l_Lean_Parser_Module_header;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module___closed__6, &l_Lean_Parser_Module_module___closed__6_once, _init_l_Lean_Parser_Module_module___closed__6);
x_2 = lean_unsigned_to_nat(1024u);
x_3 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_4 = l_Lean_Parser_leadingNode(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module___closed__7, &l_Lean_Parser_Module_module___closed__7_once, _init_l_Lean_Parser_Module_module___closed__7);
x_2 = lean_obj_once(&l_Lean_Parser_Module_module___closed__0, &l_Lean_Parser_Module_module___closed__0_once, _init_l_Lean_Parser_Module_module___closed__0);
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module___closed__8, &l_Lean_Parser_Module_module___closed__8_once, _init_l_Lean_Parser_Module_module___closed__8);
x_2 = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Module_module(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Parser_Module_module___closed__9, &l_Lean_Parser_Module_module___closed__9_once, _init_l_Lean_Parser_Module_module___closed__9);
return x_1;
}
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Module_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_moduleTk = _init_l_Lean_Parser_Module_moduleTk();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean_mark_persistent(l_Lean_Parser_Module_prelude);
l_Lean_Parser_Module_public = _init_l_Lean_Parser_Module_public();
lean_mark_persistent(l_Lean_Parser_Module_public);
l_Lean_Parser_Module_meta = _init_l_Lean_Parser_Module_meta();
lean_mark_persistent(l_Lean_Parser_Module_meta);
l_Lean_Parser_Module_all = _init_l_Lean_Parser_Module_all();
lean_mark_persistent(l_Lean_Parser_Module_all);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean_mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean_mark_persistent(l_Lean_Parser_Module_header);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_module = _init_l_Lean_Parser_Module_module();
lean_mark_persistent(l_Lean_Parser_Module_module);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Module_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Module_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Module_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
