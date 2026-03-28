// Lean compiler output
// Module: Lake.DSL.Syntax
// Imports: public import Lake.DSL.DeclUtil
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lake_DSL_declValDo;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_DSL_simpleBinder;
extern lean_object* l_Lake_DSL_identOrStr;
extern lean_object* l_Lake_DSL_optConfig;
static const lean_string_object l_Lake_DSL_nameConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_DSL_nameConst___closed__0 = (const lean_object*)&l_Lake_DSL_nameConst___closed__0_value;
static const lean_string_object l_Lake_DSL_nameConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_DSL_nameConst___closed__1 = (const lean_object*)&l_Lake_DSL_nameConst___closed__1_value;
static const lean_string_object l_Lake_DSL_nameConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nameConst"};
static const lean_object* l_Lake_DSL_nameConst___closed__2 = (const lean_object*)&l_Lake_DSL_nameConst___closed__2_value;
static const lean_ctor_object l_Lake_DSL_nameConst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_nameConst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_nameConst___closed__3_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_nameConst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_nameConst___closed__3_value_aux_1),((lean_object*)&l_Lake_DSL_nameConst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 245, 76, 54, 29, 98, 170)}};
static const lean_object* l_Lake_DSL_nameConst___closed__3 = (const lean_object*)&l_Lake_DSL_nameConst___closed__3_value;
static const lean_string_object l_Lake_DSL_nameConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__name__"};
static const lean_object* l_Lake_DSL_nameConst___closed__4 = (const lean_object*)&l_Lake_DSL_nameConst___closed__4_value;
static const lean_ctor_object l_Lake_DSL_nameConst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_nameConst___closed__4_value)}};
static const lean_object* l_Lake_DSL_nameConst___closed__5 = (const lean_object*)&l_Lake_DSL_nameConst___closed__5_value;
static const lean_ctor_object l_Lake_DSL_nameConst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_nameConst___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__5_value)}};
static const lean_object* l_Lake_DSL_nameConst___closed__6 = (const lean_object*)&l_Lake_DSL_nameConst___closed__6_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_nameConst = (const lean_object*)&l_Lake_DSL_nameConst___closed__6_value;
static const lean_string_object l_Lake_DSL_dirConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dirConst"};
static const lean_object* l_Lake_DSL_dirConst___closed__0 = (const lean_object*)&l_Lake_DSL_dirConst___closed__0_value;
static const lean_ctor_object l_Lake_DSL_dirConst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_dirConst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_dirConst___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_dirConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_dirConst___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_dirConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 238, 150, 168, 55, 12, 135, 204)}};
static const lean_object* l_Lake_DSL_dirConst___closed__1 = (const lean_object*)&l_Lake_DSL_dirConst___closed__1_value;
static const lean_string_object l_Lake_DSL_dirConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "__dir__"};
static const lean_object* l_Lake_DSL_dirConst___closed__2 = (const lean_object*)&l_Lake_DSL_dirConst___closed__2_value;
static const lean_ctor_object l_Lake_DSL_dirConst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_dirConst___closed__2_value)}};
static const lean_object* l_Lake_DSL_dirConst___closed__3 = (const lean_object*)&l_Lake_DSL_dirConst___closed__3_value;
static const lean_ctor_object l_Lake_DSL_dirConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_dirConst___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lake_DSL_dirConst___closed__3_value)}};
static const lean_object* l_Lake_DSL_dirConst___closed__4 = (const lean_object*)&l_Lake_DSL_dirConst___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_dirConst = (const lean_object*)&l_Lake_DSL_dirConst___closed__4_value;
static const lean_string_object l_Lake_DSL_getConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "getConfig"};
static const lean_object* l_Lake_DSL_getConfig___closed__0 = (const lean_object*)&l_Lake_DSL_getConfig___closed__0_value;
static const lean_ctor_object l_Lake_DSL_getConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_getConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_getConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_getConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 0, 210, 145, 234, 91, 2, 92)}};
static const lean_object* l_Lake_DSL_getConfig___closed__1 = (const lean_object*)&l_Lake_DSL_getConfig___closed__1_value;
static const lean_string_object l_Lake_DSL_getConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_DSL_getConfig___closed__2 = (const lean_object*)&l_Lake_DSL_getConfig___closed__2_value;
static const lean_ctor_object l_Lake_DSL_getConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_getConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_DSL_getConfig___closed__3 = (const lean_object*)&l_Lake_DSL_getConfig___closed__3_value;
static const lean_string_object l_Lake_DSL_getConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "get_config\? "};
static const lean_object* l_Lake_DSL_getConfig___closed__4 = (const lean_object*)&l_Lake_DSL_getConfig___closed__4_value;
static const lean_ctor_object l_Lake_DSL_getConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__4_value)}};
static const lean_object* l_Lake_DSL_getConfig___closed__5 = (const lean_object*)&l_Lake_DSL_getConfig___closed__5_value;
static const lean_string_object l_Lake_DSL_getConfig___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_DSL_getConfig___closed__6 = (const lean_object*)&l_Lake_DSL_getConfig___closed__6_value;
static const lean_ctor_object l_Lake_DSL_getConfig___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_getConfig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_DSL_getConfig___closed__7 = (const lean_object*)&l_Lake_DSL_getConfig___closed__7_value;
static const lean_ctor_object l_Lake_DSL_getConfig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__7_value)}};
static const lean_object* l_Lake_DSL_getConfig___closed__8 = (const lean_object*)&l_Lake_DSL_getConfig___closed__8_value;
static const lean_ctor_object l_Lake_DSL_getConfig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_getConfig___closed__5_value),((lean_object*)&l_Lake_DSL_getConfig___closed__8_value)}};
static const lean_object* l_Lake_DSL_getConfig___closed__9 = (const lean_object*)&l_Lake_DSL_getConfig___closed__9_value;
static const lean_ctor_object l_Lake_DSL_getConfig___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_DSL_getConfig___closed__9_value)}};
static const lean_object* l_Lake_DSL_getConfig___closed__10 = (const lean_object*)&l_Lake_DSL_getConfig___closed__10_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_getConfig = (const lean_object*)&l_Lake_DSL_getConfig___closed__10_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "packageCommand"};
static const lean_object* l_Lake_DSL_packageCommand___closed__0 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__0_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_packageCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 253, 85, 92, 174, 10, 50)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__1 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__1_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lake_DSL_packageCommand___closed__2 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__2_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__3 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__3_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_DSL_packageCommand___closed__4 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__4_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageCommand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__5 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__5_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__5_value)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__6 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__6_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__6_value)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__7 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__7_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_DSL_packageCommand___closed__8 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__8_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_DSL_packageCommand___closed__9 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__9_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_DSL_packageCommand___closed__10 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__10_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lake_DSL_packageCommand___closed__11 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__11_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_packageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__12_value_aux_1),((lean_object*)&l_Lake_DSL_packageCommand___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__12_value_aux_2),((lean_object*)&l_Lake_DSL_packageCommand___closed__11_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__12 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__12_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__12_value)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__13 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__13_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__13_value)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__14 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__14_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__7_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__14_value)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__15 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__15_value;
static const lean_string_object l_Lake_DSL_packageCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "package "};
static const lean_object* l_Lake_DSL_packageCommand___closed__16 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__16_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__16_value)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__17 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__17_value;
static const lean_ctor_object l_Lake_DSL_packageCommand___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__17_value)}};
static const lean_object* l_Lake_DSL_packageCommand___closed__18 = (const lean_object*)&l_Lake_DSL_packageCommand___closed__18_value;
static lean_once_cell_t l_Lake_DSL_packageCommand___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_packageCommand___closed__19;
static lean_once_cell_t l_Lake_DSL_packageCommand___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_packageCommand___closed__20;
static lean_once_cell_t l_Lake_DSL_packageCommand___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_packageCommand___closed__21;
static lean_once_cell_t l_Lake_DSL_packageCommand___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_packageCommand___closed__22;
LEAN_EXPORT lean_object* l_Lake_DSL_packageCommand;
LEAN_EXPORT lean_object* l_Lake_DSL_instCoePackageCommandCommand___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_DSL_instCoePackageCommandCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_instCoePackageCommandCommand___closed__0 = (const lean_object*)&l_Lake_DSL_instCoePackageCommandCommand___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_instCoePackageCommandCommand = (const lean_object*)&l_Lake_DSL_instCoePackageCommandCommand___closed__0_value;
static const lean_string_object l_Lake_DSL_postUpdateDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateDecl"};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__0 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__0_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 217, 106, 51, 176, 161, 152, 100)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__1 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__1_value;
static const lean_string_object l_Lake_DSL_postUpdateDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "post_update "};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__2 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__2_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__2_value)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__3 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__3_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__3_value)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__4 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__4_value;
static const lean_string_object l_Lake_DSL_postUpdateDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__5 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__5_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__6 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__6_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__6_value)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__7 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__7_value;
static lean_once_cell_t l_Lake_DSL_postUpdateDecl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__8;
static lean_once_cell_t l_Lake_DSL_postUpdateDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__9;
static lean_once_cell_t l_Lake_DSL_postUpdateDecl___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__10;
static const lean_string_object l_Lake_DSL_postUpdateDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__11 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__11_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__11_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__12 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__12_value;
static const lean_string_object l_Lake_DSL_postUpdateDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__13 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__13_value;
static const lean_string_object l_Lake_DSL_postUpdateDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__14 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__14_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0),((lean_object*)&l_Lake_DSL_packageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1),((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2),((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__14_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__15 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__15_value;
static const lean_ctor_object l_Lake_DSL_postUpdateDecl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__15_value)}};
static const lean_object* l_Lake_DSL_postUpdateDecl___closed__16 = (const lean_object*)&l_Lake_DSL_postUpdateDecl___closed__16_value;
static lean_once_cell_t l_Lake_DSL_postUpdateDecl___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__17;
static lean_once_cell_t l_Lake_DSL_postUpdateDecl___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__18;
static lean_once_cell_t l_Lake_DSL_postUpdateDecl___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__19;
LEAN_EXPORT lean_object* l_Lake_DSL_postUpdateDecl;
static const lean_string_object l_Lake_DSL_fromPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fromPath"};
static const lean_object* l_Lake_DSL_fromPath___closed__0 = (const lean_object*)&l_Lake_DSL_fromPath___closed__0_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_fromPath___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_fromPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_fromPath___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 231, 238, 12, 211, 124, 7, 152)}};
static const lean_object* l_Lake_DSL_fromPath___closed__1 = (const lean_object*)&l_Lake_DSL_fromPath___closed__1_value;
static const lean_string_object l_Lake_DSL_fromPath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_DSL_fromPath___closed__2 = (const lean_object*)&l_Lake_DSL_fromPath___closed__2_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_fromPath___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_DSL_fromPath___closed__3 = (const lean_object*)&l_Lake_DSL_fromPath___closed__3_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_DSL_fromPath___closed__4 = (const lean_object*)&l_Lake_DSL_fromPath___closed__4_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__0_value),((lean_object*)&l_Lake_DSL_fromPath___closed__1_value),((lean_object*)&l_Lake_DSL_fromPath___closed__4_value)}};
static const lean_object* l_Lake_DSL_fromPath___closed__5 = (const lean_object*)&l_Lake_DSL_fromPath___closed__5_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_fromPath = (const lean_object*)&l_Lake_DSL_fromPath___closed__5_value;
static const lean_string_object l_Lake_DSL_fromGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fromGit"};
static const lean_object* l_Lake_DSL_fromGit___closed__0 = (const lean_object*)&l_Lake_DSL_fromGit___closed__0_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_fromGit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromGit___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_fromGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromGit___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_fromGit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 198, 35, 138, 239, 183, 90, 121)}};
static const lean_object* l_Lake_DSL_fromGit___closed__1 = (const lean_object*)&l_Lake_DSL_fromGit___closed__1_value;
static const lean_string_object l_Lake_DSL_fromGit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "git "};
static const lean_object* l_Lake_DSL_fromGit___closed__2 = (const lean_object*)&l_Lake_DSL_fromGit___closed__2_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lake_DSL_fromGit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_DSL_fromGit___closed__3 = (const lean_object*)&l_Lake_DSL_fromGit___closed__3_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lake_DSL_fromGit___closed__4 = (const lean_object*)&l_Lake_DSL_fromGit___closed__4_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__4_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__5 = (const lean_object*)&l_Lake_DSL_fromGit___closed__5_value;
static const lean_string_object l_Lake_DSL_fromGit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Lake_DSL_fromGit___closed__6 = (const lean_object*)&l_Lake_DSL_fromGit___closed__6_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_fromGit___closed__6_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__7 = (const lean_object*)&l_Lake_DSL_fromGit___closed__7_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__7_value),((lean_object*)&l_Lake_DSL_fromGit___closed__4_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__8 = (const lean_object*)&l_Lake_DSL_fromGit___closed__8_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__8_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__9 = (const lean_object*)&l_Lake_DSL_fromGit___closed__9_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__5_value),((lean_object*)&l_Lake_DSL_fromGit___closed__9_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__10 = (const lean_object*)&l_Lake_DSL_fromGit___closed__10_value;
static const lean_string_object l_Lake_DSL_fromGit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_DSL_fromGit___closed__11 = (const lean_object*)&l_Lake_DSL_fromGit___closed__11_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_fromGit___closed__11_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__12 = (const lean_object*)&l_Lake_DSL_fromGit___closed__12_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__12_value),((lean_object*)&l_Lake_DSL_fromPath___closed__4_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__13 = (const lean_object*)&l_Lake_DSL_fromGit___closed__13_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__13_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__14 = (const lean_object*)&l_Lake_DSL_fromGit___closed__14_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__10_value),((lean_object*)&l_Lake_DSL_fromGit___closed__14_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__15 = (const lean_object*)&l_Lake_DSL_fromGit___closed__15_value;
static const lean_ctor_object l_Lake_DSL_fromGit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_fromGit___closed__0_value),((lean_object*)&l_Lake_DSL_fromGit___closed__1_value),((lean_object*)&l_Lake_DSL_fromGit___closed__15_value)}};
static const lean_object* l_Lake_DSL_fromGit___closed__16 = (const lean_object*)&l_Lake_DSL_fromGit___closed__16_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_fromGit = (const lean_object*)&l_Lake_DSL_fromGit___closed__16_value;
static const lean_string_object l_Lake_DSL_fromSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromSource"};
static const lean_object* l_Lake_DSL_fromSource___closed__0 = (const lean_object*)&l_Lake_DSL_fromSource___closed__0_value;
static const lean_ctor_object l_Lake_DSL_fromSource___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_fromSource___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromSource___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_fromSource___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromSource___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_fromSource___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 238, 246, 101, 8, 76, 68, 147)}};
static const lean_object* l_Lake_DSL_fromSource___closed__1 = (const lean_object*)&l_Lake_DSL_fromSource___closed__1_value;
static const lean_ctor_object l_Lake_DSL_fromSource___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__12_value),((lean_object*)&l_Lake_DSL_fromGit___closed__16_value),((lean_object*)&l_Lake_DSL_fromPath___closed__5_value)}};
static const lean_object* l_Lake_DSL_fromSource___closed__2 = (const lean_object*)&l_Lake_DSL_fromSource___closed__2_value;
static const lean_ctor_object l_Lake_DSL_fromSource___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_fromSource___closed__0_value),((lean_object*)&l_Lake_DSL_fromSource___closed__1_value),((lean_object*)&l_Lake_DSL_fromSource___closed__2_value)}};
static const lean_object* l_Lake_DSL_fromSource___closed__3 = (const lean_object*)&l_Lake_DSL_fromSource___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_fromSource = (const lean_object*)&l_Lake_DSL_fromSource___closed__3_value;
static const lean_string_object l_Lake_DSL_fromClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromClause"};
static const lean_object* l_Lake_DSL_fromClause___closed__0 = (const lean_object*)&l_Lake_DSL_fromClause___closed__0_value;
static const lean_ctor_object l_Lake_DSL_fromClause___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_fromClause___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromClause___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_fromClause___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_fromClause___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_fromClause___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 123, 128, 15, 141, 170, 246, 11)}};
static const lean_object* l_Lake_DSL_fromClause___closed__1 = (const lean_object*)&l_Lake_DSL_fromClause___closed__1_value;
static const lean_string_object l_Lake_DSL_fromClause___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " from "};
static const lean_object* l_Lake_DSL_fromClause___closed__2 = (const lean_object*)&l_Lake_DSL_fromClause___closed__2_value;
static const lean_ctor_object l_Lake_DSL_fromClause___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_fromClause___closed__2_value)}};
static const lean_object* l_Lake_DSL_fromClause___closed__3 = (const lean_object*)&l_Lake_DSL_fromClause___closed__3_value;
static const lean_ctor_object l_Lake_DSL_fromClause___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromClause___closed__3_value),((lean_object*)&l_Lake_DSL_fromSource___closed__3_value)}};
static const lean_object* l_Lake_DSL_fromClause___closed__4 = (const lean_object*)&l_Lake_DSL_fromClause___closed__4_value;
static const lean_ctor_object l_Lake_DSL_fromClause___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_fromClause___closed__0_value),((lean_object*)&l_Lake_DSL_fromClause___closed__1_value),((lean_object*)&l_Lake_DSL_fromClause___closed__4_value)}};
static const lean_object* l_Lake_DSL_fromClause___closed__5 = (const lean_object*)&l_Lake_DSL_fromClause___closed__5_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_fromClause = (const lean_object*)&l_Lake_DSL_fromClause___closed__5_value;
static const lean_string_object l_Lake_DSL_withClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "withClause"};
static const lean_object* l_Lake_DSL_withClause___closed__0 = (const lean_object*)&l_Lake_DSL_withClause___closed__0_value;
static const lean_ctor_object l_Lake_DSL_withClause___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_withClause___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_withClause___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_withClause___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_withClause___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_withClause___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 242, 50, 31, 135, 230, 200, 221)}};
static const lean_object* l_Lake_DSL_withClause___closed__1 = (const lean_object*)&l_Lake_DSL_withClause___closed__1_value;
static const lean_string_object l_Lake_DSL_withClause___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lake_DSL_withClause___closed__2 = (const lean_object*)&l_Lake_DSL_withClause___closed__2_value;
static const lean_ctor_object l_Lake_DSL_withClause___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_withClause___closed__2_value)}};
static const lean_object* l_Lake_DSL_withClause___closed__3 = (const lean_object*)&l_Lake_DSL_withClause___closed__3_value;
static const lean_ctor_object l_Lake_DSL_withClause___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_withClause___closed__3_value),((lean_object*)&l_Lake_DSL_fromPath___closed__4_value)}};
static const lean_object* l_Lake_DSL_withClause___closed__4 = (const lean_object*)&l_Lake_DSL_withClause___closed__4_value;
static const lean_ctor_object l_Lake_DSL_withClause___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_withClause___closed__0_value),((lean_object*)&l_Lake_DSL_withClause___closed__1_value),((lean_object*)&l_Lake_DSL_withClause___closed__4_value)}};
static const lean_object* l_Lake_DSL_withClause___closed__5 = (const lean_object*)&l_Lake_DSL_withClause___closed__5_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_withClause = (const lean_object*)&l_Lake_DSL_withClause___closed__5_value;
static const lean_string_object l_Lake_DSL_verSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verSpec"};
static const lean_object* l_Lake_DSL_verSpec___closed__0 = (const lean_object*)&l_Lake_DSL_verSpec___closed__0_value;
static const lean_ctor_object l_Lake_DSL_verSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_verSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verSpec___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_verSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verSpec___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_verSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 204, 227, 250, 63, 151, 124, 47)}};
static const lean_object* l_Lake_DSL_verSpec___closed__1 = (const lean_object*)&l_Lake_DSL_verSpec___closed__1_value;
static const lean_ctor_object l_Lake_DSL_verSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__3_value)}};
static const lean_object* l_Lake_DSL_verSpec___closed__2 = (const lean_object*)&l_Lake_DSL_verSpec___closed__2_value;
static const lean_ctor_object l_Lake_DSL_verSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_verSpec___closed__2_value),((lean_object*)&l_Lake_DSL_fromGit___closed__4_value)}};
static const lean_object* l_Lake_DSL_verSpec___closed__3 = (const lean_object*)&l_Lake_DSL_verSpec___closed__3_value;
static const lean_ctor_object l_Lake_DSL_verSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_verSpec___closed__0_value),((lean_object*)&l_Lake_DSL_verSpec___closed__1_value),((lean_object*)&l_Lake_DSL_verSpec___closed__3_value)}};
static const lean_object* l_Lake_DSL_verSpec___closed__4 = (const lean_object*)&l_Lake_DSL_verSpec___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_verSpec = (const lean_object*)&l_Lake_DSL_verSpec___closed__4_value;
static const lean_string_object l_Lake_DSL_verClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "verClause"};
static const lean_object* l_Lake_DSL_verClause___closed__0 = (const lean_object*)&l_Lake_DSL_verClause___closed__0_value;
static const lean_ctor_object l_Lake_DSL_verClause___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_verClause___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verClause___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_verClause___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verClause___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_verClause___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 114, 66, 152, 98, 148, 165, 231)}};
static const lean_object* l_Lake_DSL_verClause___closed__1 = (const lean_object*)&l_Lake_DSL_verClause___closed__1_value;
static const lean_string_object l_Lake_DSL_verClause___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l_Lake_DSL_verClause___closed__2 = (const lean_object*)&l_Lake_DSL_verClause___closed__2_value;
static const lean_ctor_object l_Lake_DSL_verClause___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_verClause___closed__2_value)}};
static const lean_object* l_Lake_DSL_verClause___closed__3 = (const lean_object*)&l_Lake_DSL_verClause___closed__3_value;
static const lean_ctor_object l_Lake_DSL_verClause___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_verClause___closed__3_value),((lean_object*)&l_Lake_DSL_verSpec___closed__4_value)}};
static const lean_object* l_Lake_DSL_verClause___closed__4 = (const lean_object*)&l_Lake_DSL_verClause___closed__4_value;
static const lean_ctor_object l_Lake_DSL_verClause___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_verClause___closed__0_value),((lean_object*)&l_Lake_DSL_verClause___closed__1_value),((lean_object*)&l_Lake_DSL_verClause___closed__4_value)}};
static const lean_object* l_Lake_DSL_verClause___closed__5 = (const lean_object*)&l_Lake_DSL_verClause___closed__5_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_verClause = (const lean_object*)&l_Lake_DSL_verClause___closed__5_value;
static const lean_string_object l_Lake_DSL_depName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depName"};
static const lean_object* l_Lake_DSL_depName___closed__0 = (const lean_object*)&l_Lake_DSL_depName___closed__0_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_depName___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_depName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_depName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 76, 0, 7, 47, 106, 167, 185)}};
static const lean_object* l_Lake_DSL_depName___closed__1 = (const lean_object*)&l_Lake_DSL_depName___closed__1_value;
static const lean_string_object l_Lake_DSL_depName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lake_DSL_depName___closed__2 = (const lean_object*)&l_Lake_DSL_depName___closed__2_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_depName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lake_DSL_depName___closed__3 = (const lean_object*)&l_Lake_DSL_depName___closed__3_value;
static const lean_string_object l_Lake_DSL_depName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lake_DSL_depName___closed__4 = (const lean_object*)&l_Lake_DSL_depName___closed__4_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_depName___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lake_DSL_depName___closed__5 = (const lean_object*)&l_Lake_DSL_depName___closed__5_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__5_value)}};
static const lean_object* l_Lake_DSL_depName___closed__6 = (const lean_object*)&l_Lake_DSL_depName___closed__6_value;
static const lean_string_object l_Lake_DSL_depName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " / "};
static const lean_object* l_Lake_DSL_depName___closed__7 = (const lean_object*)&l_Lake_DSL_depName___closed__7_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__7_value)}};
static const lean_object* l_Lake_DSL_depName___closed__8 = (const lean_object*)&l_Lake_DSL_depName___closed__8_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_depName___closed__6_value),((lean_object*)&l_Lake_DSL_depName___closed__8_value)}};
static const lean_object* l_Lake_DSL_depName___closed__9 = (const lean_object*)&l_Lake_DSL_depName___closed__9_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__3_value),((lean_object*)&l_Lake_DSL_depName___closed__9_value)}};
static const lean_object* l_Lake_DSL_depName___closed__10 = (const lean_object*)&l_Lake_DSL_depName___closed__10_value;
static const lean_ctor_object l_Lake_DSL_depName___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_depName___closed__10_value)}};
static const lean_object* l_Lake_DSL_depName___closed__11 = (const lean_object*)&l_Lake_DSL_depName___closed__11_value;
static lean_once_cell_t l_Lake_DSL_depName___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_depName___closed__12;
static lean_once_cell_t l_Lake_DSL_depName___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_depName___closed__13;
LEAN_EXPORT lean_object* l_Lake_DSL_depName;
static const lean_string_object l_Lake_DSL_depSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depSpec"};
static const lean_object* l_Lake_DSL_depSpec___closed__0 = (const lean_object*)&l_Lake_DSL_depSpec___closed__0_value;
static const lean_ctor_object l_Lake_DSL_depSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_depSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depSpec___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_depSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depSpec___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_depSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 11, 239, 15, 0, 67, 249, 1)}};
static const lean_object* l_Lake_DSL_depSpec___closed__1 = (const lean_object*)&l_Lake_DSL_depSpec___closed__1_value;
static const lean_ctor_object l_Lake_DSL_depSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_verClause___closed__5_value)}};
static const lean_object* l_Lake_DSL_depSpec___closed__2 = (const lean_object*)&l_Lake_DSL_depSpec___closed__2_value;
static lean_once_cell_t l_Lake_DSL_depSpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_depSpec___closed__3;
static const lean_ctor_object l_Lake_DSL_depSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_fromClause___closed__5_value)}};
static const lean_object* l_Lake_DSL_depSpec___closed__4 = (const lean_object*)&l_Lake_DSL_depSpec___closed__4_value;
static lean_once_cell_t l_Lake_DSL_depSpec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_depSpec___closed__5;
static const lean_ctor_object l_Lake_DSL_depSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_withClause___closed__5_value)}};
static const lean_object* l_Lake_DSL_depSpec___closed__6 = (const lean_object*)&l_Lake_DSL_depSpec___closed__6_value;
static lean_once_cell_t l_Lake_DSL_depSpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_depSpec___closed__7;
static lean_once_cell_t l_Lake_DSL_depSpec___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_depSpec___closed__8;
LEAN_EXPORT lean_object* l_Lake_DSL_depSpec;
static const lean_string_object l_Lake_DSL_requireDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "requireDecl"};
static const lean_object* l_Lake_DSL_requireDecl___closed__0 = (const lean_object*)&l_Lake_DSL_requireDecl___closed__0_value;
static const lean_ctor_object l_Lake_DSL_requireDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_requireDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_requireDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_requireDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_requireDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_requireDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 86, 225, 163, 119, 172, 216, 31)}};
static const lean_object* l_Lake_DSL_requireDecl___closed__1 = (const lean_object*)&l_Lake_DSL_requireDecl___closed__1_value;
static const lean_string_object l_Lake_DSL_requireDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "require "};
static const lean_object* l_Lake_DSL_requireDecl___closed__2 = (const lean_object*)&l_Lake_DSL_requireDecl___closed__2_value;
static const lean_ctor_object l_Lake_DSL_requireDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_requireDecl___closed__2_value)}};
static const lean_object* l_Lake_DSL_requireDecl___closed__3 = (const lean_object*)&l_Lake_DSL_requireDecl___closed__3_value;
static const lean_ctor_object l_Lake_DSL_requireDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__7_value),((lean_object*)&l_Lake_DSL_requireDecl___closed__3_value)}};
static const lean_object* l_Lake_DSL_requireDecl___closed__4 = (const lean_object*)&l_Lake_DSL_requireDecl___closed__4_value;
static lean_once_cell_t l_Lake_DSL_requireDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_requireDecl___closed__5;
static lean_once_cell_t l_Lake_DSL_requireDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_requireDecl___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_requireDecl;
LEAN_EXPORT const lean_object* l_Lake_DSL_instCoeRequireDeclCommand = (const lean_object*)&l_Lake_DSL_instCoePackageCommandCommand___closed__0_value;
static const lean_string_object l_Lake_DSL_buildDeclSig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "buildDeclSig"};
static const lean_object* l_Lake_DSL_buildDeclSig___closed__0 = (const lean_object*)&l_Lake_DSL_buildDeclSig___closed__0_value;
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_buildDeclSig___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_buildDeclSig___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_buildDeclSig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 196, 135, 185, 88, 103, 114, 194)}};
static const lean_object* l_Lake_DSL_buildDeclSig___closed__1 = (const lean_object*)&l_Lake_DSL_buildDeclSig___closed__1_value;
static lean_once_cell_t l_Lake_DSL_buildDeclSig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_buildDeclSig___closed__2;
static const lean_string_object l_Lake_DSL_buildDeclSig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_DSL_buildDeclSig___closed__3 = (const lean_object*)&l_Lake_DSL_buildDeclSig___closed__3_value;
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_buildDeclSig___closed__4_value_aux_0),((lean_object*)&l_Lake_DSL_packageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_buildDeclSig___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_packageCommand___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_buildDeclSig___closed__4_value_aux_2),((lean_object*)&l_Lake_DSL_buildDeclSig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lake_DSL_buildDeclSig___closed__4 = (const lean_object*)&l_Lake_DSL_buildDeclSig___closed__4_value;
static const lean_ctor_object l_Lake_DSL_buildDeclSig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_buildDeclSig___closed__4_value)}};
static const lean_object* l_Lake_DSL_buildDeclSig___closed__5 = (const lean_object*)&l_Lake_DSL_buildDeclSig___closed__5_value;
static lean_once_cell_t l_Lake_DSL_buildDeclSig___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_buildDeclSig___closed__6;
static lean_once_cell_t l_Lake_DSL_buildDeclSig___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_buildDeclSig___closed__7;
static lean_once_cell_t l_Lake_DSL_buildDeclSig___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_buildDeclSig___closed__8;
LEAN_EXPORT lean_object* l_Lake_DSL_buildDeclSig;
static const lean_string_object l_Lake_DSL_moduleFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "moduleFacetDecl"};
static const lean_object* l_Lake_DSL_moduleFacetDecl___closed__0 = (const lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__0_value;
static const lean_ctor_object l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_moduleFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 43, 74, 179, 42, 185, 17, 154)}};
static const lean_object* l_Lake_DSL_moduleFacetDecl___closed__1 = (const lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__1_value;
static const lean_string_object l_Lake_DSL_moduleFacetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "module_facet "};
static const lean_object* l_Lake_DSL_moduleFacetDecl___closed__2 = (const lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__2_value;
static const lean_ctor_object l_Lake_DSL_moduleFacetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__2_value)}};
static const lean_object* l_Lake_DSL_moduleFacetDecl___closed__3 = (const lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__3_value;
static const lean_ctor_object l_Lake_DSL_moduleFacetDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__3_value)}};
static const lean_object* l_Lake_DSL_moduleFacetDecl___closed__4 = (const lean_object*)&l_Lake_DSL_moduleFacetDecl___closed__4_value;
static lean_once_cell_t l_Lake_DSL_moduleFacetDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__5;
static lean_once_cell_t l_Lake_DSL_moduleFacetDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_moduleFacetDecl;
static const lean_string_object l_Lake_DSL_packageFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageFacetDecl"};
static const lean_object* l_Lake_DSL_packageFacetDecl___closed__0 = (const lean_object*)&l_Lake_DSL_packageFacetDecl___closed__0_value;
static const lean_ctor_object l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_packageFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_packageFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 92, 181, 116, 139, 59, 115, 98)}};
static const lean_object* l_Lake_DSL_packageFacetDecl___closed__1 = (const lean_object*)&l_Lake_DSL_packageFacetDecl___closed__1_value;
static const lean_string_object l_Lake_DSL_packageFacetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "package_facet "};
static const lean_object* l_Lake_DSL_packageFacetDecl___closed__2 = (const lean_object*)&l_Lake_DSL_packageFacetDecl___closed__2_value;
static const lean_ctor_object l_Lake_DSL_packageFacetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_packageFacetDecl___closed__2_value)}};
static const lean_object* l_Lake_DSL_packageFacetDecl___closed__3 = (const lean_object*)&l_Lake_DSL_packageFacetDecl___closed__3_value;
static const lean_ctor_object l_Lake_DSL_packageFacetDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_packageFacetDecl___closed__3_value)}};
static const lean_object* l_Lake_DSL_packageFacetDecl___closed__4 = (const lean_object*)&l_Lake_DSL_packageFacetDecl___closed__4_value;
static lean_once_cell_t l_Lake_DSL_packageFacetDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__5;
static lean_once_cell_t l_Lake_DSL_packageFacetDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_packageFacetDecl;
static const lean_string_object l_Lake_DSL_libraryFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libraryFacetDecl"};
static const lean_object* l_Lake_DSL_libraryFacetDecl___closed__0 = (const lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__0_value;
static const lean_ctor_object l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_libraryFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 169, 186, 57, 250, 57, 9, 172)}};
static const lean_object* l_Lake_DSL_libraryFacetDecl___closed__1 = (const lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__1_value;
static const lean_string_object l_Lake_DSL_libraryFacetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "library_facet "};
static const lean_object* l_Lake_DSL_libraryFacetDecl___closed__2 = (const lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__2_value;
static const lean_ctor_object l_Lake_DSL_libraryFacetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__2_value)}};
static const lean_object* l_Lake_DSL_libraryFacetDecl___closed__3 = (const lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__3_value;
static const lean_ctor_object l_Lake_DSL_libraryFacetDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__3_value)}};
static const lean_object* l_Lake_DSL_libraryFacetDecl___closed__4 = (const lean_object*)&l_Lake_DSL_libraryFacetDecl___closed__4_value;
static lean_once_cell_t l_Lake_DSL_libraryFacetDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__5;
static lean_once_cell_t l_Lake_DSL_libraryFacetDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_libraryFacetDecl;
static const lean_string_object l_Lake_DSL_targetCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "targetCommand"};
static const lean_object* l_Lake_DSL_targetCommand___closed__0 = (const lean_object*)&l_Lake_DSL_targetCommand___closed__0_value;
static const lean_ctor_object l_Lake_DSL_targetCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_targetCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_targetCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_targetCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_targetCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_targetCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 4, 31, 14, 49, 110, 122, 182)}};
static const lean_object* l_Lake_DSL_targetCommand___closed__1 = (const lean_object*)&l_Lake_DSL_targetCommand___closed__1_value;
static const lean_string_object l_Lake_DSL_targetCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "target "};
static const lean_object* l_Lake_DSL_targetCommand___closed__2 = (const lean_object*)&l_Lake_DSL_targetCommand___closed__2_value;
static const lean_ctor_object l_Lake_DSL_targetCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_targetCommand___closed__2_value)}};
static const lean_object* l_Lake_DSL_targetCommand___closed__3 = (const lean_object*)&l_Lake_DSL_targetCommand___closed__3_value;
static const lean_ctor_object l_Lake_DSL_targetCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_targetCommand___closed__3_value)}};
static const lean_object* l_Lake_DSL_targetCommand___closed__4 = (const lean_object*)&l_Lake_DSL_targetCommand___closed__4_value;
static lean_once_cell_t l_Lake_DSL_targetCommand___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_targetCommand___closed__5;
static lean_once_cell_t l_Lake_DSL_targetCommand___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_targetCommand___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_targetCommand;
static const lean_string_object l_Lake_DSL_leanLibCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "leanLibCommand"};
static const lean_object* l_Lake_DSL_leanLibCommand___closed__0 = (const lean_object*)&l_Lake_DSL_leanLibCommand___closed__0_value;
static const lean_ctor_object l_Lake_DSL_leanLibCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_leanLibCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_leanLibCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_leanLibCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_leanLibCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_leanLibCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 85, 99, 177, 237, 29, 129, 161)}};
static const lean_object* l_Lake_DSL_leanLibCommand___closed__1 = (const lean_object*)&l_Lake_DSL_leanLibCommand___closed__1_value;
static const lean_string_object l_Lake_DSL_leanLibCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lean_lib "};
static const lean_object* l_Lake_DSL_leanLibCommand___closed__2 = (const lean_object*)&l_Lake_DSL_leanLibCommand___closed__2_value;
static const lean_ctor_object l_Lake_DSL_leanLibCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_leanLibCommand___closed__2_value)}};
static const lean_object* l_Lake_DSL_leanLibCommand___closed__3 = (const lean_object*)&l_Lake_DSL_leanLibCommand___closed__3_value;
static const lean_ctor_object l_Lake_DSL_leanLibCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_leanLibCommand___closed__3_value)}};
static const lean_object* l_Lake_DSL_leanLibCommand___closed__4 = (const lean_object*)&l_Lake_DSL_leanLibCommand___closed__4_value;
static lean_once_cell_t l_Lake_DSL_leanLibCommand___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_leanLibCommand___closed__5;
static lean_once_cell_t l_Lake_DSL_leanLibCommand___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_leanLibCommand___closed__6;
static lean_once_cell_t l_Lake_DSL_leanLibCommand___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_leanLibCommand___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_leanLibCommand;
LEAN_EXPORT const lean_object* l_Lake_DSL_instCoeLeanLibCommandCommand = (const lean_object*)&l_Lake_DSL_instCoePackageCommandCommand___closed__0_value;
static const lean_string_object l_Lake_DSL_leanExeCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "leanExeCommand"};
static const lean_object* l_Lake_DSL_leanExeCommand___closed__0 = (const lean_object*)&l_Lake_DSL_leanExeCommand___closed__0_value;
static const lean_ctor_object l_Lake_DSL_leanExeCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_leanExeCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_leanExeCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_leanExeCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_leanExeCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_leanExeCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 151, 142, 11, 47, 160, 28)}};
static const lean_object* l_Lake_DSL_leanExeCommand___closed__1 = (const lean_object*)&l_Lake_DSL_leanExeCommand___closed__1_value;
static const lean_string_object l_Lake_DSL_leanExeCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lean_exe "};
static const lean_object* l_Lake_DSL_leanExeCommand___closed__2 = (const lean_object*)&l_Lake_DSL_leanExeCommand___closed__2_value;
static const lean_ctor_object l_Lake_DSL_leanExeCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_leanExeCommand___closed__2_value)}};
static const lean_object* l_Lake_DSL_leanExeCommand___closed__3 = (const lean_object*)&l_Lake_DSL_leanExeCommand___closed__3_value;
static const lean_ctor_object l_Lake_DSL_leanExeCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_leanExeCommand___closed__3_value)}};
static const lean_object* l_Lake_DSL_leanExeCommand___closed__4 = (const lean_object*)&l_Lake_DSL_leanExeCommand___closed__4_value;
static lean_once_cell_t l_Lake_DSL_leanExeCommand___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_leanExeCommand___closed__5;
static lean_once_cell_t l_Lake_DSL_leanExeCommand___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_leanExeCommand___closed__6;
static lean_once_cell_t l_Lake_DSL_leanExeCommand___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_leanExeCommand___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_leanExeCommand;
LEAN_EXPORT const lean_object* l_Lake_DSL_instCoeLeanExeCommandCommand = (const lean_object*)&l_Lake_DSL_instCoePackageCommandCommand___closed__0_value;
static const lean_string_object l_Lake_DSL_inputFileCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inputFileCommand"};
static const lean_object* l_Lake_DSL_inputFileCommand___closed__0 = (const lean_object*)&l_Lake_DSL_inputFileCommand___closed__0_value;
static const lean_ctor_object l_Lake_DSL_inputFileCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_inputFileCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_inputFileCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_inputFileCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_inputFileCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_inputFileCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 35, 118, 98, 33, 135, 119, 140)}};
static const lean_object* l_Lake_DSL_inputFileCommand___closed__1 = (const lean_object*)&l_Lake_DSL_inputFileCommand___closed__1_value;
static const lean_string_object l_Lake_DSL_inputFileCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "input_file "};
static const lean_object* l_Lake_DSL_inputFileCommand___closed__2 = (const lean_object*)&l_Lake_DSL_inputFileCommand___closed__2_value;
static const lean_ctor_object l_Lake_DSL_inputFileCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_inputFileCommand___closed__2_value)}};
static const lean_object* l_Lake_DSL_inputFileCommand___closed__3 = (const lean_object*)&l_Lake_DSL_inputFileCommand___closed__3_value;
static const lean_ctor_object l_Lake_DSL_inputFileCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_inputFileCommand___closed__3_value)}};
static const lean_object* l_Lake_DSL_inputFileCommand___closed__4 = (const lean_object*)&l_Lake_DSL_inputFileCommand___closed__4_value;
static lean_once_cell_t l_Lake_DSL_inputFileCommand___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_inputFileCommand___closed__5;
static lean_once_cell_t l_Lake_DSL_inputFileCommand___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_inputFileCommand___closed__6;
static lean_once_cell_t l_Lake_DSL_inputFileCommand___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_inputFileCommand___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_inputFileCommand;
LEAN_EXPORT const lean_object* l_Lake_DSL_instCoeInputFileCommandCommand = (const lean_object*)&l_Lake_DSL_instCoePackageCommandCommand___closed__0_value;
static const lean_string_object l_Lake_DSL_inputDirCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inputDirCommand"};
static const lean_object* l_Lake_DSL_inputDirCommand___closed__0 = (const lean_object*)&l_Lake_DSL_inputDirCommand___closed__0_value;
static const lean_ctor_object l_Lake_DSL_inputDirCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_inputDirCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_inputDirCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_inputDirCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_inputDirCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_inputDirCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 99, 104, 48, 39, 151, 172, 112)}};
static const lean_object* l_Lake_DSL_inputDirCommand___closed__1 = (const lean_object*)&l_Lake_DSL_inputDirCommand___closed__1_value;
static const lean_string_object l_Lake_DSL_inputDirCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "input_dir "};
static const lean_object* l_Lake_DSL_inputDirCommand___closed__2 = (const lean_object*)&l_Lake_DSL_inputDirCommand___closed__2_value;
static const lean_ctor_object l_Lake_DSL_inputDirCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_inputDirCommand___closed__2_value)}};
static const lean_object* l_Lake_DSL_inputDirCommand___closed__3 = (const lean_object*)&l_Lake_DSL_inputDirCommand___closed__3_value;
static const lean_ctor_object l_Lake_DSL_inputDirCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_inputDirCommand___closed__3_value)}};
static const lean_object* l_Lake_DSL_inputDirCommand___closed__4 = (const lean_object*)&l_Lake_DSL_inputDirCommand___closed__4_value;
static lean_once_cell_t l_Lake_DSL_inputDirCommand___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_inputDirCommand___closed__5;
static lean_once_cell_t l_Lake_DSL_inputDirCommand___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_inputDirCommand___closed__6;
static lean_once_cell_t l_Lake_DSL_inputDirCommand___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_inputDirCommand___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_inputDirCommand;
LEAN_EXPORT const lean_object* l_Lake_DSL_instCoeInputDirCommandCommand = (const lean_object*)&l_Lake_DSL_instCoePackageCommandCommand___closed__0_value;
static const lean_string_object l_Lake_DSL_externLibDeclSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "externLibDeclSpec"};
static const lean_object* l_Lake_DSL_externLibDeclSpec___closed__0 = (const lean_object*)&l_Lake_DSL_externLibDeclSpec___closed__0_value;
static const lean_ctor_object l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_externLibDeclSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_externLibDeclSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 47, 189, 11, 205, 24, 206, 176)}};
static const lean_object* l_Lake_DSL_externLibDeclSpec___closed__1 = (const lean_object*)&l_Lake_DSL_externLibDeclSpec___closed__1_value;
static lean_once_cell_t l_Lake_DSL_externLibDeclSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_externLibDeclSpec___closed__2;
static lean_once_cell_t l_Lake_DSL_externLibDeclSpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_externLibDeclSpec___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_externLibDeclSpec;
static const lean_string_object l_Lake_DSL_externLibCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "externLibCommand"};
static const lean_object* l_Lake_DSL_externLibCommand___closed__0 = (const lean_object*)&l_Lake_DSL_externLibCommand___closed__0_value;
static const lean_ctor_object l_Lake_DSL_externLibCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_externLibCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_externLibCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_externLibCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_externLibCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_externLibCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 102, 133, 13, 61, 107, 230, 129)}};
static const lean_object* l_Lake_DSL_externLibCommand___closed__1 = (const lean_object*)&l_Lake_DSL_externLibCommand___closed__1_value;
static const lean_string_object l_Lake_DSL_externLibCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extern_lib "};
static const lean_object* l_Lake_DSL_externLibCommand___closed__2 = (const lean_object*)&l_Lake_DSL_externLibCommand___closed__2_value;
static const lean_ctor_object l_Lake_DSL_externLibCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_externLibCommand___closed__2_value)}};
static const lean_object* l_Lake_DSL_externLibCommand___closed__3 = (const lean_object*)&l_Lake_DSL_externLibCommand___closed__3_value;
static const lean_ctor_object l_Lake_DSL_externLibCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_externLibCommand___closed__3_value)}};
static const lean_object* l_Lake_DSL_externLibCommand___closed__4 = (const lean_object*)&l_Lake_DSL_externLibCommand___closed__4_value;
static lean_once_cell_t l_Lake_DSL_externLibCommand___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_externLibCommand___closed__5;
static lean_once_cell_t l_Lake_DSL_externLibCommand___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_externLibCommand___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_externLibCommand;
static const lean_string_object l_Lake_DSL_scriptDeclSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "scriptDeclSpec"};
static const lean_object* l_Lake_DSL_scriptDeclSpec___closed__0 = (const lean_object*)&l_Lake_DSL_scriptDeclSpec___closed__0_value;
static const lean_ctor_object l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_scriptDeclSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_scriptDeclSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 145, 50, 108, 63, 62, 118, 110)}};
static const lean_object* l_Lake_DSL_scriptDeclSpec___closed__1 = (const lean_object*)&l_Lake_DSL_scriptDeclSpec___closed__1_value;
static lean_once_cell_t l_Lake_DSL_scriptDeclSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_scriptDeclSpec___closed__2;
static lean_once_cell_t l_Lake_DSL_scriptDeclSpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_scriptDeclSpec___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_scriptDeclSpec;
static const lean_string_object l_Lake_DSL_scriptDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scriptDecl"};
static const lean_object* l_Lake_DSL_scriptDecl___closed__0 = (const lean_object*)&l_Lake_DSL_scriptDecl___closed__0_value;
static const lean_ctor_object l_Lake_DSL_scriptDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_scriptDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_scriptDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_scriptDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_scriptDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_scriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 18, 40, 229, 14, 216, 222, 158)}};
static const lean_object* l_Lake_DSL_scriptDecl___closed__1 = (const lean_object*)&l_Lake_DSL_scriptDecl___closed__1_value;
static const lean_string_object l_Lake_DSL_scriptDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "script "};
static const lean_object* l_Lake_DSL_scriptDecl___closed__2 = (const lean_object*)&l_Lake_DSL_scriptDecl___closed__2_value;
static const lean_ctor_object l_Lake_DSL_scriptDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_scriptDecl___closed__2_value)}};
static const lean_object* l_Lake_DSL_scriptDecl___closed__3 = (const lean_object*)&l_Lake_DSL_scriptDecl___closed__3_value;
static const lean_ctor_object l_Lake_DSL_scriptDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageCommand___closed__15_value),((lean_object*)&l_Lake_DSL_scriptDecl___closed__3_value)}};
static const lean_object* l_Lake_DSL_scriptDecl___closed__4 = (const lean_object*)&l_Lake_DSL_scriptDecl___closed__4_value;
static lean_once_cell_t l_Lake_DSL_scriptDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_scriptDecl___closed__5;
static lean_once_cell_t l_Lake_DSL_scriptDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_scriptDecl___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_scriptDecl;
static const lean_string_object l_Lake_DSL_verLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "verLit"};
static const lean_object* l_Lake_DSL_verLit___closed__0 = (const lean_object*)&l_Lake_DSL_verLit___closed__0_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_verLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verLit___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_verLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verLit___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_verLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 205, 236, 50, 125, 9, 172, 134)}};
static const lean_object* l_Lake_DSL_verLit___closed__1 = (const lean_object*)&l_Lake_DSL_verLit___closed__1_value;
static const lean_string_object l_Lake_DSL_verLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "v!"};
static const lean_object* l_Lake_DSL_verLit___closed__2 = (const lean_object*)&l_Lake_DSL_verLit___closed__2_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_verLit___closed__2_value)}};
static const lean_object* l_Lake_DSL_verLit___closed__3 = (const lean_object*)&l_Lake_DSL_verLit___closed__3_value;
static const lean_string_object l_Lake_DSL_verLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l_Lake_DSL_verLit___closed__4 = (const lean_object*)&l_Lake_DSL_verLit___closed__4_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_verLit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l_Lake_DSL_verLit___closed__5 = (const lean_object*)&l_Lake_DSL_verLit___closed__5_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_verLit___closed__5_value)}};
static const lean_object* l_Lake_DSL_verLit___closed__6 = (const lean_object*)&l_Lake_DSL_verLit___closed__6_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value)}};
static const lean_object* l_Lake_DSL_verLit___closed__7 = (const lean_object*)&l_Lake_DSL_verLit___closed__7_value;
static const lean_string_object l_Lake_DSL_verLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lake_DSL_verLit___closed__8 = (const lean_object*)&l_Lake_DSL_verLit___closed__8_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_verLit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lake_DSL_verLit___closed__9 = (const lean_object*)&l_Lake_DSL_verLit___closed__9_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verLit___closed__9_value),((lean_object*)&l_Lake_DSL_fromPath___closed__4_value)}};
static const lean_object* l_Lake_DSL_verLit___closed__10 = (const lean_object*)&l_Lake_DSL_verLit___closed__10_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__7_value),((lean_object*)&l_Lake_DSL_verLit___closed__10_value)}};
static const lean_object* l_Lake_DSL_verLit___closed__11 = (const lean_object*)&l_Lake_DSL_verLit___closed__11_value;
static const lean_ctor_object l_Lake_DSL_verLit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_verLit___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lake_DSL_verLit___closed__11_value)}};
static const lean_object* l_Lake_DSL_verLit___closed__12 = (const lean_object*)&l_Lake_DSL_verLit___closed__12_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_verLit = (const lean_object*)&l_Lake_DSL_verLit___closed__12_value;
static const lean_string_object l_Lake_DSL_facetSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "facetSuffix"};
static const lean_object* l_Lake_DSL_facetSuffix___closed__0 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__0_value;
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_facetSuffix___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_facetSuffix___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_facetSuffix___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 19, 148, 195, 91, 53, 9, 109)}};
static const lean_object* l_Lake_DSL_facetSuffix___closed__1 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__1_value;
static const lean_string_object l_Lake_DSL_facetSuffix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_DSL_facetSuffix___closed__2 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__2_value;
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_facetSuffix___closed__2_value)}};
static const lean_object* l_Lake_DSL_facetSuffix___closed__3 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__3_value;
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_facetSuffix___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value)}};
static const lean_object* l_Lake_DSL_facetSuffix___closed__4 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__4_value;
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__3_value),((lean_object*)&l_Lake_DSL_facetSuffix___closed__4_value)}};
static const lean_object* l_Lake_DSL_facetSuffix___closed__5 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__5_value;
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_facetSuffix___closed__5_value),((lean_object*)&l_Lake_DSL_getConfig___closed__8_value)}};
static const lean_object* l_Lake_DSL_facetSuffix___closed__6 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__6_value;
static const lean_ctor_object l_Lake_DSL_facetSuffix___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_facetSuffix___closed__0_value),((lean_object*)&l_Lake_DSL_facetSuffix___closed__1_value),((lean_object*)&l_Lake_DSL_facetSuffix___closed__6_value)}};
static const lean_object* l_Lake_DSL_facetSuffix___closed__7 = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__7_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_facetSuffix = (const lean_object*)&l_Lake_DSL_facetSuffix___closed__7_value;
static const lean_string_object l_Lake_DSL_packageTargetLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageTargetLit"};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__0 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__0_value;
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetLit___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetLit___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 101, 186, 35, 177, 203, 61, 85)}};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__1 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__1_value;
static const lean_string_object l_Lake_DSL_packageTargetLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__2 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__2_value;
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetLit___closed__2_value)}};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__3 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__3_value;
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value)}};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__4 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__4_value;
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__4_value)}};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__5 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__5_value;
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__5_value)}};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__6 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__6_value;
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__6_value),((lean_object*)&l_Lake_DSL_getConfig___closed__8_value)}};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__7 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__7_value;
static const lean_ctor_object l_Lake_DSL_packageTargetLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetLit___closed__0_value),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__1_value),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__7_value)}};
static const lean_object* l_Lake_DSL_packageTargetLit___closed__8 = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__8_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_packageTargetLit = (const lean_object*)&l_Lake_DSL_packageTargetLit___closed__8_value;
static const lean_string_object l_Lake_DSL_moduleTargetKeyLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "moduleTargetKeyLit"};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__0 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__0_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 150, 87, 20, 34, 170, 193, 64)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__1 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__1_value;
static const lean_string_object l_Lake_DSL_moduleTargetKeyLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`+"};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__2 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__2_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__2_value)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__3 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__3_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__4 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__4_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__4_value),((lean_object*)&l_Lake_DSL_getConfig___closed__8_value)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__5 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__5_value;
static const lean_string_object l_Lake_DSL_moduleTargetKeyLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__6 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__6_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__6_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__7 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__7_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__7_value),((lean_object*)&l_Lake_DSL_facetSuffix___closed__7_value)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__8 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__8_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__5_value),((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__8_value)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__9 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__9_value;
static const lean_ctor_object l_Lake_DSL_moduleTargetKeyLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__9_value)}};
static const lean_object* l_Lake_DSL_moduleTargetKeyLit___closed__10 = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__10_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_moduleTargetKeyLit = (const lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__10_value;
static const lean_string_object l_Lake_DSL_packageTargetKeyLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "packageTargetKeyLit"};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__0 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__0_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 78, 171, 75, 222, 86, 241, 235)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__1 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__1_value;
static const lean_string_object l_Lake_DSL_packageTargetKeyLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`@"};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__2 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__2_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__2_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__3 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__3_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value),((lean_object*)&l_Lake_DSL_getConfig___closed__8_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__4 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__4_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__4_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__5 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__5_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__5_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__6 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__6_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value),((lean_object*)&l_Lake_DSL_fromGit___closed__12_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__7 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__7_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__7_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__8 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__8_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_depName___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__8_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__9 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__9_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__9_value),((lean_object*)&l_Lake_DSL_packageTargetLit___closed__8_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__10 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__10_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__10_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__11 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__11_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__6_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__11_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__12 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__12_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_verLit___closed__6_value),((lean_object*)&l_Lake_DSL_facetSuffix___closed__7_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__13 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__13_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_moduleTargetKeyLit___closed__7_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__13_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__14 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__14_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__12_value),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__14_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__15 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__15_value;
static const lean_ctor_object l_Lake_DSL_packageTargetKeyLit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__15_value)}};
static const lean_object* l_Lake_DSL_packageTargetKeyLit___closed__16 = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__16_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_packageTargetKeyLit = (const lean_object*)&l_Lake_DSL_packageTargetKeyLit___closed__16_value;
static const lean_string_object l_Lake_DSL_cmdDo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cmdDo"};
static const lean_object* l_Lake_DSL_cmdDo___closed__0 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__0_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_cmdDo___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_cmdDo___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_cmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 39, 184, 30, 65, 63, 201, 66)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__1 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__1_value;
static const lean_string_object l_Lake_DSL_cmdDo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lake_DSL_cmdDo___closed__2 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__2_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_cmdDo___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__3 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__3_value;
static const lean_string_object l_Lake_DSL_cmdDo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lake_DSL_cmdDo___closed__4 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__4_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_cmdDo___closed__4_value)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__5 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__5_value;
static const lean_string_object l_Lake_DSL_cmdDo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "many1Indent"};
static const lean_object* l_Lake_DSL_cmdDo___closed__6 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__6_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_cmdDo___closed__6_value),LEAN_SCALAR_PTR_LITERAL(161, 232, 149, 52, 5, 17, 36, 232)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__7 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__7_value;
static const lean_string_object l_Lake_DSL_cmdDo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lake_DSL_cmdDo___closed__8 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__8_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_cmdDo___closed__8_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__9 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__9_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_DSL_cmdDo___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_DSL_cmdDo___closed__10 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__10_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_cmdDo___closed__7_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__10_value)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__11 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__11_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__5_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__11_value)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__12 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__12_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_cmdDo___closed__3_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__12_value)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__13 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__13_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__12_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__13_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__10_value)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__14 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__14_value;
static const lean_ctor_object l_Lake_DSL_cmdDo___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_cmdDo___closed__0_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__1_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__14_value)}};
static const lean_object* l_Lake_DSL_cmdDo___closed__15 = (const lean_object*)&l_Lake_DSL_cmdDo___closed__15_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_cmdDo = (const lean_object*)&l_Lake_DSL_cmdDo___closed__15_value;
static const lean_string_object l_Lake_DSL_metaIf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "metaIf"};
static const lean_object* l_Lake_DSL_metaIf___closed__0 = (const lean_object*)&l_Lake_DSL_metaIf___closed__0_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_metaIf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_metaIf___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_metaIf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_metaIf___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_metaIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 98, 156, 191, 205, 206, 20, 202)}};
static const lean_object* l_Lake_DSL_metaIf___closed__1 = (const lean_object*)&l_Lake_DSL_metaIf___closed__1_value;
static const lean_string_object l_Lake_DSL_metaIf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta "};
static const lean_object* l_Lake_DSL_metaIf___closed__2 = (const lean_object*)&l_Lake_DSL_metaIf___closed__2_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_metaIf___closed__2_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__3 = (const lean_object*)&l_Lake_DSL_metaIf___closed__3_value;
static const lean_string_object l_Lake_DSL_metaIf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "if "};
static const lean_object* l_Lake_DSL_metaIf___closed__4 = (const lean_object*)&l_Lake_DSL_metaIf___closed__4_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_metaIf___closed__4_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__5 = (const lean_object*)&l_Lake_DSL_metaIf___closed__5_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__5_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__6 = (const lean_object*)&l_Lake_DSL_metaIf___closed__6_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__6_value),((lean_object*)&l_Lake_DSL_fromPath___closed__4_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__7 = (const lean_object*)&l_Lake_DSL_metaIf___closed__7_value;
static const lean_string_object l_Lake_DSL_metaIf___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " then "};
static const lean_object* l_Lake_DSL_metaIf___closed__8 = (const lean_object*)&l_Lake_DSL_metaIf___closed__8_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_metaIf___closed__8_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__9 = (const lean_object*)&l_Lake_DSL_metaIf___closed__9_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__7_value),((lean_object*)&l_Lake_DSL_metaIf___closed__9_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__10 = (const lean_object*)&l_Lake_DSL_metaIf___closed__10_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__10_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__15_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__11 = (const lean_object*)&l_Lake_DSL_metaIf___closed__11_value;
static const lean_string_object l_Lake_DSL_metaIf___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " else "};
static const lean_object* l_Lake_DSL_metaIf___closed__12 = (const lean_object*)&l_Lake_DSL_metaIf___closed__12_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_metaIf___closed__12_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__13 = (const lean_object*)&l_Lake_DSL_metaIf___closed__13_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__13_value),((lean_object*)&l_Lake_DSL_cmdDo___closed__15_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__14 = (const lean_object*)&l_Lake_DSL_metaIf___closed__14_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__14_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__15 = (const lean_object*)&l_Lake_DSL_metaIf___closed__15_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__11_value),((lean_object*)&l_Lake_DSL_metaIf___closed__15_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__16 = (const lean_object*)&l_Lake_DSL_metaIf___closed__16_value;
static const lean_ctor_object l_Lake_DSL_metaIf___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_metaIf___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_DSL_metaIf___closed__16_value)}};
static const lean_object* l_Lake_DSL_metaIf___closed__17 = (const lean_object*)&l_Lake_DSL_metaIf___closed__17_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_metaIf = (const lean_object*)&l_Lake_DSL_metaIf___closed__17_value;
static const lean_string_object l_Lake_DSL_runIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "runIO"};
static const lean_object* l_Lake_DSL_runIO___closed__0 = (const lean_object*)&l_Lake_DSL_runIO___closed__0_value;
static const lean_ctor_object l_Lake_DSL_runIO___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_runIO___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_runIO___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_runIO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_runIO___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_runIO___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 189, 119, 141, 116, 67, 96, 12)}};
static const lean_object* l_Lake_DSL_runIO___closed__1 = (const lean_object*)&l_Lake_DSL_runIO___closed__1_value;
static const lean_string_object l_Lake_DSL_runIO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "run_io "};
static const lean_object* l_Lake_DSL_runIO___closed__2 = (const lean_object*)&l_Lake_DSL_runIO___closed__2_value;
static const lean_ctor_object l_Lake_DSL_runIO___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_runIO___closed__2_value)}};
static const lean_object* l_Lake_DSL_runIO___closed__3 = (const lean_object*)&l_Lake_DSL_runIO___closed__3_value;
static const lean_string_object l_Lake_DSL_runIO___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doSeq"};
static const lean_object* l_Lake_DSL_runIO___closed__4 = (const lean_object*)&l_Lake_DSL_runIO___closed__4_value;
static const lean_ctor_object l_Lake_DSL_runIO___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_runIO___closed__4_value),LEAN_SCALAR_PTR_LITERAL(87, 108, 208, 147, 238, 58, 86, 179)}};
static const lean_object* l_Lake_DSL_runIO___closed__5 = (const lean_object*)&l_Lake_DSL_runIO___closed__5_value;
static const lean_ctor_object l_Lake_DSL_runIO___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_runIO___closed__5_value)}};
static const lean_object* l_Lake_DSL_runIO___closed__6 = (const lean_object*)&l_Lake_DSL_runIO___closed__6_value;
static const lean_ctor_object l_Lake_DSL_runIO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_runIO___closed__3_value),((lean_object*)&l_Lake_DSL_runIO___closed__6_value)}};
static const lean_object* l_Lake_DSL_runIO___closed__7 = (const lean_object*)&l_Lake_DSL_runIO___closed__7_value;
static const lean_ctor_object l_Lake_DSL_runIO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_runIO___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_DSL_runIO___closed__7_value)}};
static const lean_object* l_Lake_DSL_runIO___closed__8 = (const lean_object*)&l_Lake_DSL_runIO___closed__8_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_runIO = (const lean_object*)&l_Lake_DSL_runIO___closed__8_value;
static lean_object* _init_l_Lake_DSL_packageCommand___closed__19(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = l_Lake_DSL_identOrStr;
v___x_96_ = ((lean_object*)(l_Lake_DSL_packageCommand___closed__3));
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__20(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_99_ = ((lean_object*)(l_Lake_DSL_packageCommand___closed__18));
v___x_100_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_101_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__21(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = l_Lake_DSL_optConfig;
v___x_103_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__20, &l_Lake_DSL_packageCommand___closed__20_once, _init_l_Lake_DSL_packageCommand___closed__20);
v___x_104_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_105_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
lean_ctor_set(v___x_105_, 2, v___x_102_);
return v___x_105_;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__22(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__21, &l_Lake_DSL_packageCommand___closed__21_once, _init_l_Lake_DSL_packageCommand___closed__21);
v___x_107_ = lean_unsigned_to_nat(1022u);
v___x_108_ = ((lean_object*)(l_Lake_DSL_packageCommand___closed__1));
v___x_109_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
lean_ctor_set(v___x_109_, 2, v___x_106_);
return v___x_109_;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__22, &l_Lake_DSL_packageCommand___closed__22_once, _init_l_Lake_DSL_packageCommand___closed__22);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_instCoePackageCommandCommand___lam__0(lean_object* v_x_111_){
_start:
{
lean_inc(v_x_111_);
return v_x_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed(lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lake_DSL_instCoePackageCommandCommand___lam__0(v_x_112_);
lean_dec(v_x_112_);
return v_res_113_;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__8(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = l_Lake_DSL_simpleBinder;
v___x_134_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__7));
v___x_135_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_136_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
return v___x_136_;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__9(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__8, &l_Lake_DSL_postUpdateDecl___closed__8_once, _init_l_Lake_DSL_postUpdateDecl___closed__8);
v___x_138_ = ((lean_object*)(l_Lake_DSL_packageCommand___closed__3));
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__10(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__9, &l_Lake_DSL_postUpdateDecl___closed__9_once, _init_l_Lake_DSL_postUpdateDecl___closed__9);
v___x_141_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__4));
v___x_142_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_143_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_140_);
return v___x_143_;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__17(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = l_Lake_DSL_declValDo;
v___x_157_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__16));
v___x_158_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__12));
v___x_159_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__18(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__17, &l_Lake_DSL_postUpdateDecl___closed__17_once, _init_l_Lake_DSL_postUpdateDecl___closed__17);
v___x_161_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__10, &l_Lake_DSL_postUpdateDecl___closed__10_once, _init_l_Lake_DSL_postUpdateDecl___closed__10);
v___x_162_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_163_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__19(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__18, &l_Lake_DSL_postUpdateDecl___closed__18_once, _init_l_Lake_DSL_postUpdateDecl___closed__18);
v___x_165_ = lean_unsigned_to_nat(1022u);
v___x_166_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__1));
v___x_167_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
lean_ctor_set(v___x_167_, 2, v___x_164_);
return v___x_167_;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__19, &l_Lake_DSL_postUpdateDecl___closed__19_once, _init_l_Lake_DSL_postUpdateDecl___closed__19);
return v___x_168_;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__12(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = l_Lake_DSL_identOrStr;
v___x_343_ = ((lean_object*)(l_Lake_DSL_depName___closed__11));
v___x_344_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_345_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_342_);
return v___x_345_;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__13(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_obj_once(&l_Lake_DSL_depName___closed__12, &l_Lake_DSL_depName___closed__12_once, _init_l_Lake_DSL_depName___closed__12);
v___x_347_ = ((lean_object*)(l_Lake_DSL_depName___closed__1));
v___x_348_ = ((lean_object*)(l_Lake_DSL_depName___closed__0));
v___x_349_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_346_);
return v___x_349_;
}
}
static lean_object* _init_l_Lake_DSL_depName(void){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lake_DSL_depName___closed__13, &l_Lake_DSL_depName___closed__13_once, _init_l_Lake_DSL_depName___closed__13);
return v___x_350_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__3(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__2));
v___x_360_ = l_Lake_DSL_depName;
v___x_361_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_362_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_360_);
lean_ctor_set(v___x_362_, 2, v___x_359_);
return v___x_362_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__5(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__4));
v___x_367_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__3, &l_Lake_DSL_depSpec___closed__3_once, _init_l_Lake_DSL_depSpec___closed__3);
v___x_368_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_369_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
lean_ctor_set(v___x_369_, 2, v___x_366_);
return v___x_369_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__7(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__6));
v___x_374_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__5, &l_Lake_DSL_depSpec___closed__5_once, _init_l_Lake_DSL_depSpec___closed__5);
v___x_375_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_376_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_373_);
return v___x_376_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__8(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__7, &l_Lake_DSL_depSpec___closed__7_once, _init_l_Lake_DSL_depSpec___closed__7);
v___x_378_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__1));
v___x_379_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__0));
v___x_380_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
lean_ctor_set(v___x_380_, 2, v___x_377_);
return v___x_380_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__8, &l_Lake_DSL_depSpec___closed__8_once, _init_l_Lake_DSL_depSpec___closed__8);
return v___x_381_;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__5(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = l_Lake_DSL_depSpec;
v___x_395_ = ((lean_object*)(l_Lake_DSL_requireDecl___closed__4));
v___x_396_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_397_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_394_);
return v___x_397_;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__6(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_398_ = lean_obj_once(&l_Lake_DSL_requireDecl___closed__5, &l_Lake_DSL_requireDecl___closed__5_once, _init_l_Lake_DSL_requireDecl___closed__5);
v___x_399_ = lean_unsigned_to_nat(1022u);
v___x_400_ = ((lean_object*)(l_Lake_DSL_requireDecl___closed__1));
v___x_401_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_398_);
return v___x_401_;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_obj_once(&l_Lake_DSL_requireDecl___closed__6, &l_Lake_DSL_requireDecl___closed__6_once, _init_l_Lake_DSL_requireDecl___closed__6);
return v___x_402_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__2(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__9, &l_Lake_DSL_postUpdateDecl___closed__9_once, _init_l_Lake_DSL_postUpdateDecl___closed__9);
v___x_410_ = l_Lake_DSL_identOrStr;
v___x_411_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_412_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
return v___x_412_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__6(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = ((lean_object*)(l_Lake_DSL_buildDeclSig___closed__5));
v___x_422_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__2, &l_Lake_DSL_buildDeclSig___closed__2_once, _init_l_Lake_DSL_buildDeclSig___closed__2);
v___x_423_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_424_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
lean_ctor_set(v___x_424_, 2, v___x_421_);
return v___x_424_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__7(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_425_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__16));
v___x_426_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__6, &l_Lake_DSL_buildDeclSig___closed__6_once, _init_l_Lake_DSL_buildDeclSig___closed__6);
v___x_427_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_428_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_425_);
return v___x_428_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__8(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__7, &l_Lake_DSL_buildDeclSig___closed__7_once, _init_l_Lake_DSL_buildDeclSig___closed__7);
v___x_430_ = ((lean_object*)(l_Lake_DSL_buildDeclSig___closed__1));
v___x_431_ = ((lean_object*)(l_Lake_DSL_buildDeclSig___closed__0));
v___x_432_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_429_);
return v___x_432_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig(void){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__8, &l_Lake_DSL_buildDeclSig___closed__8_once, _init_l_Lake_DSL_buildDeclSig___closed__8);
return v___x_433_;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__5(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_446_ = l_Lake_DSL_buildDeclSig;
v___x_447_ = ((lean_object*)(l_Lake_DSL_moduleFacetDecl___closed__4));
v___x_448_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_449_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_446_);
return v___x_449_;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__6(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = lean_obj_once(&l_Lake_DSL_moduleFacetDecl___closed__5, &l_Lake_DSL_moduleFacetDecl___closed__5_once, _init_l_Lake_DSL_moduleFacetDecl___closed__5);
v___x_451_ = lean_unsigned_to_nat(1022u);
v___x_452_ = ((lean_object*)(l_Lake_DSL_moduleFacetDecl___closed__1));
v___x_453_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_450_);
return v___x_453_;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_obj_once(&l_Lake_DSL_moduleFacetDecl___closed__6, &l_Lake_DSL_moduleFacetDecl___closed__6_once, _init_l_Lake_DSL_moduleFacetDecl___closed__6);
return v___x_454_;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__5(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = l_Lake_DSL_buildDeclSig;
v___x_468_ = ((lean_object*)(l_Lake_DSL_packageFacetDecl___closed__4));
v___x_469_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_470_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_467_);
return v___x_470_;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__6(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_obj_once(&l_Lake_DSL_packageFacetDecl___closed__5, &l_Lake_DSL_packageFacetDecl___closed__5_once, _init_l_Lake_DSL_packageFacetDecl___closed__5);
v___x_472_ = lean_unsigned_to_nat(1022u);
v___x_473_ = ((lean_object*)(l_Lake_DSL_packageFacetDecl___closed__1));
v___x_474_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_471_);
return v___x_474_;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_obj_once(&l_Lake_DSL_packageFacetDecl___closed__6, &l_Lake_DSL_packageFacetDecl___closed__6_once, _init_l_Lake_DSL_packageFacetDecl___closed__6);
return v___x_475_;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__5(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = l_Lake_DSL_buildDeclSig;
v___x_489_ = ((lean_object*)(l_Lake_DSL_libraryFacetDecl___closed__4));
v___x_490_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_491_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_489_);
lean_ctor_set(v___x_491_, 2, v___x_488_);
return v___x_491_;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__6(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_492_ = lean_obj_once(&l_Lake_DSL_libraryFacetDecl___closed__5, &l_Lake_DSL_libraryFacetDecl___closed__5_once, _init_l_Lake_DSL_libraryFacetDecl___closed__5);
v___x_493_ = lean_unsigned_to_nat(1022u);
v___x_494_ = ((lean_object*)(l_Lake_DSL_libraryFacetDecl___closed__1));
v___x_495_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_492_);
return v___x_495_;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_obj_once(&l_Lake_DSL_libraryFacetDecl___closed__6, &l_Lake_DSL_libraryFacetDecl___closed__6_once, _init_l_Lake_DSL_libraryFacetDecl___closed__6);
return v___x_496_;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__5(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_509_ = l_Lake_DSL_buildDeclSig;
v___x_510_ = ((lean_object*)(l_Lake_DSL_targetCommand___closed__4));
v___x_511_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_512_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
lean_ctor_set(v___x_512_, 2, v___x_509_);
return v___x_512_;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__6(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_obj_once(&l_Lake_DSL_targetCommand___closed__5, &l_Lake_DSL_targetCommand___closed__5_once, _init_l_Lake_DSL_targetCommand___closed__5);
v___x_514_ = lean_unsigned_to_nat(1022u);
v___x_515_ = ((lean_object*)(l_Lake_DSL_targetCommand___closed__1));
v___x_516_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_513_);
return v___x_516_;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand(void){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l_Lake_DSL_targetCommand___closed__6, &l_Lake_DSL_targetCommand___closed__6_once, _init_l_Lake_DSL_targetCommand___closed__6);
return v___x_517_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__5(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_530_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_531_ = ((lean_object*)(l_Lake_DSL_leanLibCommand___closed__4));
v___x_532_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_533_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_530_);
return v___x_533_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__6(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = l_Lake_DSL_optConfig;
v___x_535_ = lean_obj_once(&l_Lake_DSL_leanLibCommand___closed__5, &l_Lake_DSL_leanLibCommand___closed__5_once, _init_l_Lake_DSL_leanLibCommand___closed__5);
v___x_536_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_537_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_534_);
return v___x_537_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__7(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_obj_once(&l_Lake_DSL_leanLibCommand___closed__6, &l_Lake_DSL_leanLibCommand___closed__6_once, _init_l_Lake_DSL_leanLibCommand___closed__6);
v___x_539_ = lean_unsigned_to_nat(1022u);
v___x_540_ = ((lean_object*)(l_Lake_DSL_leanLibCommand___closed__1));
v___x_541_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_539_);
lean_ctor_set(v___x_541_, 2, v___x_538_);
return v___x_541_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand(void){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lake_DSL_leanLibCommand___closed__7, &l_Lake_DSL_leanLibCommand___closed__7_once, _init_l_Lake_DSL_leanLibCommand___closed__7);
return v___x_542_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__5(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_556_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_557_ = ((lean_object*)(l_Lake_DSL_leanExeCommand___closed__4));
v___x_558_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_559_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
lean_ctor_set(v___x_559_, 2, v___x_556_);
return v___x_559_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__6(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = l_Lake_DSL_optConfig;
v___x_561_ = lean_obj_once(&l_Lake_DSL_leanExeCommand___closed__5, &l_Lake_DSL_leanExeCommand___closed__5_once, _init_l_Lake_DSL_leanExeCommand___closed__5);
v___x_562_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_563_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
lean_ctor_set(v___x_563_, 2, v___x_560_);
return v___x_563_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__7(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_564_ = lean_obj_once(&l_Lake_DSL_leanExeCommand___closed__6, &l_Lake_DSL_leanExeCommand___closed__6_once, _init_l_Lake_DSL_leanExeCommand___closed__6);
v___x_565_ = lean_unsigned_to_nat(1022u);
v___x_566_ = ((lean_object*)(l_Lake_DSL_leanExeCommand___closed__1));
v___x_567_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_565_);
lean_ctor_set(v___x_567_, 2, v___x_564_);
return v___x_567_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand(void){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Lake_DSL_leanExeCommand___closed__7, &l_Lake_DSL_leanExeCommand___closed__7_once, _init_l_Lake_DSL_leanExeCommand___closed__7);
return v___x_568_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__5(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_583_ = ((lean_object*)(l_Lake_DSL_inputFileCommand___closed__4));
v___x_584_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_585_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
lean_ctor_set(v___x_585_, 2, v___x_582_);
return v___x_585_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__6(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_586_ = l_Lake_DSL_optConfig;
v___x_587_ = lean_obj_once(&l_Lake_DSL_inputFileCommand___closed__5, &l_Lake_DSL_inputFileCommand___closed__5_once, _init_l_Lake_DSL_inputFileCommand___closed__5);
v___x_588_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_589_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
lean_ctor_set(v___x_589_, 2, v___x_586_);
return v___x_589_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__7(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = lean_obj_once(&l_Lake_DSL_inputFileCommand___closed__6, &l_Lake_DSL_inputFileCommand___closed__6_once, _init_l_Lake_DSL_inputFileCommand___closed__6);
v___x_591_ = lean_unsigned_to_nat(1022u);
v___x_592_ = ((lean_object*)(l_Lake_DSL_inputFileCommand___closed__1));
v___x_593_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
lean_ctor_set(v___x_593_, 2, v___x_590_);
return v___x_593_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lake_DSL_inputFileCommand___closed__7, &l_Lake_DSL_inputFileCommand___closed__7_once, _init_l_Lake_DSL_inputFileCommand___closed__7);
return v___x_594_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_609_ = ((lean_object*)(l_Lake_DSL_inputDirCommand___closed__4));
v___x_610_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_611_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_608_);
return v___x_611_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__6(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = l_Lake_DSL_optConfig;
v___x_613_ = lean_obj_once(&l_Lake_DSL_inputDirCommand___closed__5, &l_Lake_DSL_inputDirCommand___closed__5_once, _init_l_Lake_DSL_inputDirCommand___closed__5);
v___x_614_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_615_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
lean_ctor_set(v___x_615_, 2, v___x_612_);
return v___x_615_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__7(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_616_ = lean_obj_once(&l_Lake_DSL_inputDirCommand___closed__6, &l_Lake_DSL_inputDirCommand___closed__6_once, _init_l_Lake_DSL_inputDirCommand___closed__6);
v___x_617_ = lean_unsigned_to_nat(1022u);
v___x_618_ = ((lean_object*)(l_Lake_DSL_inputDirCommand___closed__1));
v___x_619_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_616_);
return v___x_619_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Lake_DSL_inputDirCommand___closed__7, &l_Lake_DSL_inputDirCommand___closed__7_once, _init_l_Lake_DSL_inputDirCommand___closed__7);
return v___x_620_;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__2(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__16));
v___x_628_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__2, &l_Lake_DSL_buildDeclSig___closed__2_once, _init_l_Lake_DSL_buildDeclSig___closed__2);
v___x_629_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_630_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
lean_ctor_set(v___x_630_, 2, v___x_627_);
return v___x_630_;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__3(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_631_ = lean_obj_once(&l_Lake_DSL_externLibDeclSpec___closed__2, &l_Lake_DSL_externLibDeclSpec___closed__2_once, _init_l_Lake_DSL_externLibDeclSpec___closed__2);
v___x_632_ = ((lean_object*)(l_Lake_DSL_externLibDeclSpec___closed__1));
v___x_633_ = ((lean_object*)(l_Lake_DSL_externLibDeclSpec___closed__0));
v___x_634_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_631_);
return v___x_634_;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lake_DSL_externLibDeclSpec___closed__3, &l_Lake_DSL_externLibDeclSpec___closed__3_once, _init_l_Lake_DSL_externLibDeclSpec___closed__3);
return v___x_635_;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__5(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = l_Lake_DSL_externLibDeclSpec;
v___x_649_ = ((lean_object*)(l_Lake_DSL_externLibCommand___closed__4));
v___x_650_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_651_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_648_);
return v___x_651_;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__6(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_obj_once(&l_Lake_DSL_externLibCommand___closed__5, &l_Lake_DSL_externLibCommand___closed__5_once, _init_l_Lake_DSL_externLibCommand___closed__5);
v___x_653_ = lean_unsigned_to_nat(1022u);
v___x_654_ = ((lean_object*)(l_Lake_DSL_externLibCommand___closed__1));
v___x_655_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_652_);
return v___x_655_;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand(void){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lake_DSL_externLibCommand___closed__6, &l_Lake_DSL_externLibCommand___closed__6_once, _init_l_Lake_DSL_externLibCommand___closed__6);
return v___x_656_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__2(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__17, &l_Lake_DSL_postUpdateDecl___closed__17_once, _init_l_Lake_DSL_postUpdateDecl___closed__17);
v___x_663_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__2, &l_Lake_DSL_buildDeclSig___closed__2_once, _init_l_Lake_DSL_buildDeclSig___closed__2);
v___x_664_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_665_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
lean_ctor_set(v___x_665_, 2, v___x_662_);
return v___x_665_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__3(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = lean_obj_once(&l_Lake_DSL_scriptDeclSpec___closed__2, &l_Lake_DSL_scriptDeclSpec___closed__2_once, _init_l_Lake_DSL_scriptDeclSpec___closed__2);
v___x_667_ = ((lean_object*)(l_Lake_DSL_scriptDeclSpec___closed__1));
v___x_668_ = ((lean_object*)(l_Lake_DSL_scriptDeclSpec___closed__0));
v___x_669_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
lean_ctor_set(v___x_669_, 2, v___x_666_);
return v___x_669_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec(void){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l_Lake_DSL_scriptDeclSpec___closed__3, &l_Lake_DSL_scriptDeclSpec___closed__3_once, _init_l_Lake_DSL_scriptDeclSpec___closed__3);
return v___x_670_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__5(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = l_Lake_DSL_scriptDeclSpec;
v___x_684_ = ((lean_object*)(l_Lake_DSL_scriptDecl___closed__4));
v___x_685_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_686_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
lean_ctor_set(v___x_686_, 2, v___x_683_);
return v___x_686_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__6(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = lean_obj_once(&l_Lake_DSL_scriptDecl___closed__5, &l_Lake_DSL_scriptDecl___closed__5_once, _init_l_Lake_DSL_scriptDecl___closed__5);
v___x_688_ = lean_unsigned_to_nat(1022u);
v___x_689_ = ((lean_object*)(l_Lake_DSL_scriptDecl___closed__1));
v___x_690_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___x_688_);
lean_ctor_set(v___x_690_, 2, v___x_687_);
return v___x_690_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Lake_DSL_scriptDecl___closed__6, &l_Lake_DSL_scriptDecl___closed__6_once, _init_l_Lake_DSL_scriptDecl___closed__6);
return v___x_691_;
}
}
lean_object* runtime_initialize_Lake_DSL_DeclUtil(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lake_DSL_packageCommand = _init_l_Lake_DSL_packageCommand();
lean_mark_persistent(l_Lake_DSL_packageCommand);
l_Lake_DSL_postUpdateDecl = _init_l_Lake_DSL_postUpdateDecl();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl);
l_Lake_DSL_depName = _init_l_Lake_DSL_depName();
lean_mark_persistent(l_Lake_DSL_depName);
l_Lake_DSL_depSpec = _init_l_Lake_DSL_depSpec();
lean_mark_persistent(l_Lake_DSL_depSpec);
l_Lake_DSL_requireDecl = _init_l_Lake_DSL_requireDecl();
lean_mark_persistent(l_Lake_DSL_requireDecl);
l_Lake_DSL_buildDeclSig = _init_l_Lake_DSL_buildDeclSig();
lean_mark_persistent(l_Lake_DSL_buildDeclSig);
l_Lake_DSL_moduleFacetDecl = _init_l_Lake_DSL_moduleFacetDecl();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl);
l_Lake_DSL_packageFacetDecl = _init_l_Lake_DSL_packageFacetDecl();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl);
l_Lake_DSL_libraryFacetDecl = _init_l_Lake_DSL_libraryFacetDecl();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl);
l_Lake_DSL_targetCommand = _init_l_Lake_DSL_targetCommand();
lean_mark_persistent(l_Lake_DSL_targetCommand);
l_Lake_DSL_leanLibCommand = _init_l_Lake_DSL_leanLibCommand();
lean_mark_persistent(l_Lake_DSL_leanLibCommand);
l_Lake_DSL_leanExeCommand = _init_l_Lake_DSL_leanExeCommand();
lean_mark_persistent(l_Lake_DSL_leanExeCommand);
l_Lake_DSL_inputFileCommand = _init_l_Lake_DSL_inputFileCommand();
lean_mark_persistent(l_Lake_DSL_inputFileCommand);
l_Lake_DSL_inputDirCommand = _init_l_Lake_DSL_inputDirCommand();
lean_mark_persistent(l_Lake_DSL_inputDirCommand);
l_Lake_DSL_externLibDeclSpec = _init_l_Lake_DSL_externLibDeclSpec();
lean_mark_persistent(l_Lake_DSL_externLibDeclSpec);
l_Lake_DSL_externLibCommand = _init_l_Lake_DSL_externLibCommand();
lean_mark_persistent(l_Lake_DSL_externLibCommand);
l_Lake_DSL_scriptDeclSpec = _init_l_Lake_DSL_scriptDeclSpec();
lean_mark_persistent(l_Lake_DSL_scriptDeclSpec);
l_Lake_DSL_scriptDecl = _init_l_Lake_DSL_scriptDecl();
lean_mark_persistent(l_Lake_DSL_scriptDecl);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
