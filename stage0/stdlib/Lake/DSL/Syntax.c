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
static const lean_string_object l_Lake_DSL_fromPath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "copy "};
static const lean_object* l_Lake_DSL_fromPath___closed__2 = (const lean_object*)&l_Lake_DSL_fromPath___closed__2_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_DSL_fromPath___closed__3 = (const lean_object*)&l_Lake_DSL_fromPath___closed__3_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_packageCommand___closed__3_value),((lean_object*)&l_Lake_DSL_fromPath___closed__3_value)}};
static const lean_object* l_Lake_DSL_fromPath___closed__4 = (const lean_object*)&l_Lake_DSL_fromPath___closed__4_value;
static const lean_string_object l_Lake_DSL_fromPath___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_DSL_fromPath___closed__5 = (const lean_object*)&l_Lake_DSL_fromPath___closed__5_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_fromPath___closed__5_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_DSL_fromPath___closed__6 = (const lean_object*)&l_Lake_DSL_fromPath___closed__6_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_DSL_fromPath___closed__7 = (const lean_object*)&l_Lake_DSL_fromPath___closed__7_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromPath___closed__4_value),((lean_object*)&l_Lake_DSL_fromPath___closed__7_value)}};
static const lean_object* l_Lake_DSL_fromPath___closed__8 = (const lean_object*)&l_Lake_DSL_fromPath___closed__8_value;
static const lean_ctor_object l_Lake_DSL_fromPath___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__0_value),((lean_object*)&l_Lake_DSL_fromPath___closed__1_value),((lean_object*)&l_Lake_DSL_fromPath___closed__8_value)}};
static const lean_object* l_Lake_DSL_fromPath___closed__9 = (const lean_object*)&l_Lake_DSL_fromPath___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_fromPath = (const lean_object*)&l_Lake_DSL_fromPath___closed__9_value;
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
static const lean_ctor_object l_Lake_DSL_fromGit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_DSL_fromPath___closed__6_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
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
static const lean_ctor_object l_Lake_DSL_fromGit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_fromGit___closed__12_value),((lean_object*)&l_Lake_DSL_fromPath___closed__7_value)}};
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
static const lean_ctor_object l_Lake_DSL_fromSource___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_postUpdateDecl___closed__12_value),((lean_object*)&l_Lake_DSL_fromGit___closed__16_value),((lean_object*)&l_Lake_DSL_fromPath___closed__9_value)}};
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
static const lean_ctor_object l_Lake_DSL_withClause___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_withClause___closed__3_value),((lean_object*)&l_Lake_DSL_fromPath___closed__7_value)}};
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
static const lean_string_object l_Lake_DSL_evalVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalVer"};
static const lean_object* l_Lake_DSL_evalVer___closed__0 = (const lean_object*)&l_Lake_DSL_evalVer___closed__0_value;
static const lean_ctor_object l_Lake_DSL_evalVer___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_nameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_evalVer___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_evalVer___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_nameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_evalVer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_evalVer___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_evalVer___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 252, 213, 234, 103, 11, 172, 191)}};
static const lean_object* l_Lake_DSL_evalVer___closed__1 = (const lean_object*)&l_Lake_DSL_evalVer___closed__1_value;
static const lean_string_object l_Lake_DSL_evalVer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eval_ver%"};
static const lean_object* l_Lake_DSL_evalVer___closed__2 = (const lean_object*)&l_Lake_DSL_evalVer___closed__2_value;
static const lean_ctor_object l_Lake_DSL_evalVer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_evalVer___closed__2_value)}};
static const lean_object* l_Lake_DSL_evalVer___closed__3 = (const lean_object*)&l_Lake_DSL_evalVer___closed__3_value;
static const lean_ctor_object l_Lake_DSL_evalVer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_evalVer___closed__3_value),((lean_object*)&l_Lake_DSL_fromPath___closed__7_value)}};
static const lean_object* l_Lake_DSL_evalVer___closed__4 = (const lean_object*)&l_Lake_DSL_evalVer___closed__4_value;
static const lean_ctor_object l_Lake_DSL_evalVer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_DSL_evalVer___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_DSL_evalVer___closed__4_value)}};
static const lean_object* l_Lake_DSL_evalVer___closed__5 = (const lean_object*)&l_Lake_DSL_evalVer___closed__5_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_evalVer = (const lean_object*)&l_Lake_DSL_evalVer___closed__5_value;
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
static const lean_ctor_object l_Lake_DSL_verLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_verLit___closed__9_value),((lean_object*)&l_Lake_DSL_fromPath___closed__7_value)}};
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
static const lean_ctor_object l_Lake_DSL_metaIf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_getConfig___closed__3_value),((lean_object*)&l_Lake_DSL_metaIf___closed__6_value),((lean_object*)&l_Lake_DSL_fromPath___closed__7_value)}};
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
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = l_Lake_DSL_identOrStr;
v___x_354_ = ((lean_object*)(l_Lake_DSL_depName___closed__11));
v___x_355_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_356_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_353_);
return v___x_356_;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__13(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_obj_once(&l_Lake_DSL_depName___closed__12, &l_Lake_DSL_depName___closed__12_once, _init_l_Lake_DSL_depName___closed__12);
v___x_358_ = ((lean_object*)(l_Lake_DSL_depName___closed__1));
v___x_359_ = ((lean_object*)(l_Lake_DSL_depName___closed__0));
v___x_360_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
lean_ctor_set(v___x_360_, 2, v___x_357_);
return v___x_360_;
}
}
static lean_object* _init_l_Lake_DSL_depName(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lake_DSL_depName___closed__13, &l_Lake_DSL_depName___closed__13_once, _init_l_Lake_DSL_depName___closed__13);
return v___x_361_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__3(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_370_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__2));
v___x_371_ = l_Lake_DSL_depName;
v___x_372_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_373_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_370_);
return v___x_373_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__5(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__4));
v___x_378_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__3, &l_Lake_DSL_depSpec___closed__3_once, _init_l_Lake_DSL_depSpec___closed__3);
v___x_379_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_380_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
lean_ctor_set(v___x_380_, 2, v___x_377_);
return v___x_380_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__7(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__6));
v___x_385_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__5, &l_Lake_DSL_depSpec___closed__5_once, _init_l_Lake_DSL_depSpec___closed__5);
v___x_386_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_387_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
lean_ctor_set(v___x_387_, 2, v___x_384_);
return v___x_387_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__8(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__7, &l_Lake_DSL_depSpec___closed__7_once, _init_l_Lake_DSL_depSpec___closed__7);
v___x_389_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__1));
v___x_390_ = ((lean_object*)(l_Lake_DSL_depSpec___closed__0));
v___x_391_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_388_);
return v___x_391_;
}
}
static lean_object* _init_l_Lake_DSL_depSpec(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lake_DSL_depSpec___closed__8, &l_Lake_DSL_depSpec___closed__8_once, _init_l_Lake_DSL_depSpec___closed__8);
return v___x_392_;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__5(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = l_Lake_DSL_depSpec;
v___x_406_ = ((lean_object*)(l_Lake_DSL_requireDecl___closed__4));
v___x_407_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_408_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_405_);
return v___x_408_;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__6(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_obj_once(&l_Lake_DSL_requireDecl___closed__5, &l_Lake_DSL_requireDecl___closed__5_once, _init_l_Lake_DSL_requireDecl___closed__5);
v___x_410_ = lean_unsigned_to_nat(1022u);
v___x_411_ = ((lean_object*)(l_Lake_DSL_requireDecl___closed__1));
v___x_412_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
return v___x_412_;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl(void){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_obj_once(&l_Lake_DSL_requireDecl___closed__6, &l_Lake_DSL_requireDecl___closed__6_once, _init_l_Lake_DSL_requireDecl___closed__6);
return v___x_413_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__9, &l_Lake_DSL_postUpdateDecl___closed__9_once, _init_l_Lake_DSL_postUpdateDecl___closed__9);
v___x_421_ = l_Lake_DSL_identOrStr;
v___x_422_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_423_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
return v___x_423_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__6(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = ((lean_object*)(l_Lake_DSL_buildDeclSig___closed__5));
v___x_433_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__2, &l_Lake_DSL_buildDeclSig___closed__2_once, _init_l_Lake_DSL_buildDeclSig___closed__2);
v___x_434_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_435_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_432_);
return v___x_435_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__7(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__16));
v___x_437_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__6, &l_Lake_DSL_buildDeclSig___closed__6_once, _init_l_Lake_DSL_buildDeclSig___closed__6);
v___x_438_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_439_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_437_);
lean_ctor_set(v___x_439_, 2, v___x_436_);
return v___x_439_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__8(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__7, &l_Lake_DSL_buildDeclSig___closed__7_once, _init_l_Lake_DSL_buildDeclSig___closed__7);
v___x_441_ = ((lean_object*)(l_Lake_DSL_buildDeclSig___closed__1));
v___x_442_ = ((lean_object*)(l_Lake_DSL_buildDeclSig___closed__0));
v___x_443_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_440_);
return v___x_443_;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__8, &l_Lake_DSL_buildDeclSig___closed__8_once, _init_l_Lake_DSL_buildDeclSig___closed__8);
return v___x_444_;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__5(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = l_Lake_DSL_buildDeclSig;
v___x_458_ = ((lean_object*)(l_Lake_DSL_moduleFacetDecl___closed__4));
v___x_459_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_460_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
lean_ctor_set(v___x_460_, 2, v___x_457_);
return v___x_460_;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__6(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = lean_obj_once(&l_Lake_DSL_moduleFacetDecl___closed__5, &l_Lake_DSL_moduleFacetDecl___closed__5_once, _init_l_Lake_DSL_moduleFacetDecl___closed__5);
v___x_462_ = lean_unsigned_to_nat(1022u);
v___x_463_ = ((lean_object*)(l_Lake_DSL_moduleFacetDecl___closed__1));
v___x_464_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
lean_ctor_set(v___x_464_, 2, v___x_461_);
return v___x_464_;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl(void){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_obj_once(&l_Lake_DSL_moduleFacetDecl___closed__6, &l_Lake_DSL_moduleFacetDecl___closed__6_once, _init_l_Lake_DSL_moduleFacetDecl___closed__6);
return v___x_465_;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__5(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = l_Lake_DSL_buildDeclSig;
v___x_479_ = ((lean_object*)(l_Lake_DSL_packageFacetDecl___closed__4));
v___x_480_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_481_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_478_);
return v___x_481_;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__6(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_482_ = lean_obj_once(&l_Lake_DSL_packageFacetDecl___closed__5, &l_Lake_DSL_packageFacetDecl___closed__5_once, _init_l_Lake_DSL_packageFacetDecl___closed__5);
v___x_483_ = lean_unsigned_to_nat(1022u);
v___x_484_ = ((lean_object*)(l_Lake_DSL_packageFacetDecl___closed__1));
v___x_485_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_483_);
lean_ctor_set(v___x_485_, 2, v___x_482_);
return v___x_485_;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_obj_once(&l_Lake_DSL_packageFacetDecl___closed__6, &l_Lake_DSL_packageFacetDecl___closed__6_once, _init_l_Lake_DSL_packageFacetDecl___closed__6);
return v___x_486_;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__5(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_499_ = l_Lake_DSL_buildDeclSig;
v___x_500_ = ((lean_object*)(l_Lake_DSL_libraryFacetDecl___closed__4));
v___x_501_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_502_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
lean_ctor_set(v___x_502_, 2, v___x_499_);
return v___x_502_;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__6(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_obj_once(&l_Lake_DSL_libraryFacetDecl___closed__5, &l_Lake_DSL_libraryFacetDecl___closed__5_once, _init_l_Lake_DSL_libraryFacetDecl___closed__5);
v___x_504_ = lean_unsigned_to_nat(1022u);
v___x_505_ = ((lean_object*)(l_Lake_DSL_libraryFacetDecl___closed__1));
v___x_506_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_503_);
return v___x_506_;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl(void){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lake_DSL_libraryFacetDecl___closed__6, &l_Lake_DSL_libraryFacetDecl___closed__6_once, _init_l_Lake_DSL_libraryFacetDecl___closed__6);
return v___x_507_;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__5(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = l_Lake_DSL_buildDeclSig;
v___x_521_ = ((lean_object*)(l_Lake_DSL_targetCommand___closed__4));
v___x_522_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_523_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_521_);
lean_ctor_set(v___x_523_, 2, v___x_520_);
return v___x_523_;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__6(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_obj_once(&l_Lake_DSL_targetCommand___closed__5, &l_Lake_DSL_targetCommand___closed__5_once, _init_l_Lake_DSL_targetCommand___closed__5);
v___x_525_ = lean_unsigned_to_nat(1022u);
v___x_526_ = ((lean_object*)(l_Lake_DSL_targetCommand___closed__1));
v___x_527_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
lean_ctor_set(v___x_527_, 2, v___x_524_);
return v___x_527_;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Lake_DSL_targetCommand___closed__6, &l_Lake_DSL_targetCommand___closed__6_once, _init_l_Lake_DSL_targetCommand___closed__6);
return v___x_528_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__5(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_542_ = ((lean_object*)(l_Lake_DSL_leanLibCommand___closed__4));
v___x_543_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_544_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_542_);
lean_ctor_set(v___x_544_, 2, v___x_541_);
return v___x_544_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__6(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_545_ = l_Lake_DSL_optConfig;
v___x_546_ = lean_obj_once(&l_Lake_DSL_leanLibCommand___closed__5, &l_Lake_DSL_leanLibCommand___closed__5_once, _init_l_Lake_DSL_leanLibCommand___closed__5);
v___x_547_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_548_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_545_);
return v___x_548_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__7(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_549_ = lean_obj_once(&l_Lake_DSL_leanLibCommand___closed__6, &l_Lake_DSL_leanLibCommand___closed__6_once, _init_l_Lake_DSL_leanLibCommand___closed__6);
v___x_550_ = lean_unsigned_to_nat(1022u);
v___x_551_ = ((lean_object*)(l_Lake_DSL_leanLibCommand___closed__1));
v___x_552_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
lean_ctor_set(v___x_552_, 2, v___x_549_);
return v___x_552_;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand(void){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lake_DSL_leanLibCommand___closed__7, &l_Lake_DSL_leanLibCommand___closed__7_once, _init_l_Lake_DSL_leanLibCommand___closed__7);
return v___x_553_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__5(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_568_ = ((lean_object*)(l_Lake_DSL_leanExeCommand___closed__4));
v___x_569_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_570_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_567_);
return v___x_570_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__6(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = l_Lake_DSL_optConfig;
v___x_572_ = lean_obj_once(&l_Lake_DSL_leanExeCommand___closed__5, &l_Lake_DSL_leanExeCommand___closed__5_once, _init_l_Lake_DSL_leanExeCommand___closed__5);
v___x_573_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_574_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
lean_ctor_set(v___x_574_, 2, v___x_571_);
return v___x_574_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__7(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_obj_once(&l_Lake_DSL_leanExeCommand___closed__6, &l_Lake_DSL_leanExeCommand___closed__6_once, _init_l_Lake_DSL_leanExeCommand___closed__6);
v___x_576_ = lean_unsigned_to_nat(1022u);
v___x_577_ = ((lean_object*)(l_Lake_DSL_leanExeCommand___closed__1));
v___x_578_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_575_);
return v___x_578_;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_obj_once(&l_Lake_DSL_leanExeCommand___closed__7, &l_Lake_DSL_leanExeCommand___closed__7_once, _init_l_Lake_DSL_leanExeCommand___closed__7);
return v___x_579_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__5(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_593_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_594_ = ((lean_object*)(l_Lake_DSL_inputFileCommand___closed__4));
v___x_595_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_596_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
lean_ctor_set(v___x_596_, 2, v___x_593_);
return v___x_596_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__6(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = l_Lake_DSL_optConfig;
v___x_598_ = lean_obj_once(&l_Lake_DSL_inputFileCommand___closed__5, &l_Lake_DSL_inputFileCommand___closed__5_once, _init_l_Lake_DSL_inputFileCommand___closed__5);
v___x_599_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_600_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
lean_ctor_set(v___x_600_, 2, v___x_597_);
return v___x_600_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__7(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_obj_once(&l_Lake_DSL_inputFileCommand___closed__6, &l_Lake_DSL_inputFileCommand___closed__6_once, _init_l_Lake_DSL_inputFileCommand___closed__6);
v___x_602_ = lean_unsigned_to_nat(1022u);
v___x_603_ = ((lean_object*)(l_Lake_DSL_inputFileCommand___closed__1));
v___x_604_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_601_);
return v___x_604_;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Lake_DSL_inputFileCommand___closed__7, &l_Lake_DSL_inputFileCommand___closed__7_once, _init_l_Lake_DSL_inputFileCommand___closed__7);
return v___x_605_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__5(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_619_ = lean_obj_once(&l_Lake_DSL_packageCommand___closed__19, &l_Lake_DSL_packageCommand___closed__19_once, _init_l_Lake_DSL_packageCommand___closed__19);
v___x_620_ = ((lean_object*)(l_Lake_DSL_inputDirCommand___closed__4));
v___x_621_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_622_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___x_620_);
lean_ctor_set(v___x_622_, 2, v___x_619_);
return v___x_622_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__6(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = l_Lake_DSL_optConfig;
v___x_624_ = lean_obj_once(&l_Lake_DSL_inputDirCommand___closed__5, &l_Lake_DSL_inputDirCommand___closed__5_once, _init_l_Lake_DSL_inputDirCommand___closed__5);
v___x_625_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_626_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_623_);
return v___x_626_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__7(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_obj_once(&l_Lake_DSL_inputDirCommand___closed__6, &l_Lake_DSL_inputDirCommand___closed__6_once, _init_l_Lake_DSL_inputDirCommand___closed__6);
v___x_628_ = lean_unsigned_to_nat(1022u);
v___x_629_ = ((lean_object*)(l_Lake_DSL_inputDirCommand___closed__1));
v___x_630_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
lean_ctor_set(v___x_630_, 2, v___x_627_);
return v___x_630_;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_obj_once(&l_Lake_DSL_inputDirCommand___closed__7, &l_Lake_DSL_inputDirCommand___closed__7_once, _init_l_Lake_DSL_inputDirCommand___closed__7);
return v___x_631_;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__2(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = ((lean_object*)(l_Lake_DSL_postUpdateDecl___closed__16));
v___x_639_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__2, &l_Lake_DSL_buildDeclSig___closed__2_once, _init_l_Lake_DSL_buildDeclSig___closed__2);
v___x_640_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_641_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
lean_ctor_set(v___x_641_, 2, v___x_638_);
return v___x_641_;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_obj_once(&l_Lake_DSL_externLibDeclSpec___closed__2, &l_Lake_DSL_externLibDeclSpec___closed__2_once, _init_l_Lake_DSL_externLibDeclSpec___closed__2);
v___x_643_ = ((lean_object*)(l_Lake_DSL_externLibDeclSpec___closed__1));
v___x_644_ = ((lean_object*)(l_Lake_DSL_externLibDeclSpec___closed__0));
v___x_645_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_642_);
return v___x_645_;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l_Lake_DSL_externLibDeclSpec___closed__3, &l_Lake_DSL_externLibDeclSpec___closed__3_once, _init_l_Lake_DSL_externLibDeclSpec___closed__3);
return v___x_646_;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__5(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = l_Lake_DSL_externLibDeclSpec;
v___x_660_ = ((lean_object*)(l_Lake_DSL_externLibCommand___closed__4));
v___x_661_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_662_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
lean_ctor_set(v___x_662_, 2, v___x_659_);
return v___x_662_;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__6(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_663_ = lean_obj_once(&l_Lake_DSL_externLibCommand___closed__5, &l_Lake_DSL_externLibCommand___closed__5_once, _init_l_Lake_DSL_externLibCommand___closed__5);
v___x_664_ = lean_unsigned_to_nat(1022u);
v___x_665_ = ((lean_object*)(l_Lake_DSL_externLibCommand___closed__1));
v___x_666_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_664_);
lean_ctor_set(v___x_666_, 2, v___x_663_);
return v___x_666_;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand(void){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = lean_obj_once(&l_Lake_DSL_externLibCommand___closed__6, &l_Lake_DSL_externLibCommand___closed__6_once, _init_l_Lake_DSL_externLibCommand___closed__6);
return v___x_667_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__2(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_673_ = lean_obj_once(&l_Lake_DSL_postUpdateDecl___closed__17, &l_Lake_DSL_postUpdateDecl___closed__17_once, _init_l_Lake_DSL_postUpdateDecl___closed__17);
v___x_674_ = lean_obj_once(&l_Lake_DSL_buildDeclSig___closed__2, &l_Lake_DSL_buildDeclSig___closed__2_once, _init_l_Lake_DSL_buildDeclSig___closed__2);
v___x_675_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_676_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_674_);
lean_ctor_set(v___x_676_, 2, v___x_673_);
return v___x_676_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__3(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_677_ = lean_obj_once(&l_Lake_DSL_scriptDeclSpec___closed__2, &l_Lake_DSL_scriptDeclSpec___closed__2_once, _init_l_Lake_DSL_scriptDeclSpec___closed__2);
v___x_678_ = ((lean_object*)(l_Lake_DSL_scriptDeclSpec___closed__1));
v___x_679_ = ((lean_object*)(l_Lake_DSL_scriptDeclSpec___closed__0));
v___x_680_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
lean_ctor_set(v___x_680_, 2, v___x_677_);
return v___x_680_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec(void){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lake_DSL_scriptDeclSpec___closed__3, &l_Lake_DSL_scriptDeclSpec___closed__3_once, _init_l_Lake_DSL_scriptDeclSpec___closed__3);
return v___x_681_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__5(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = l_Lake_DSL_scriptDeclSpec;
v___x_695_ = ((lean_object*)(l_Lake_DSL_scriptDecl___closed__4));
v___x_696_ = ((lean_object*)(l_Lake_DSL_getConfig___closed__3));
v___x_697_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_695_);
lean_ctor_set(v___x_697_, 2, v___x_694_);
return v___x_697_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__6(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = lean_obj_once(&l_Lake_DSL_scriptDecl___closed__5, &l_Lake_DSL_scriptDecl___closed__5_once, _init_l_Lake_DSL_scriptDecl___closed__5);
v___x_699_ = lean_unsigned_to_nat(1022u);
v___x_700_ = ((lean_object*)(l_Lake_DSL_scriptDecl___closed__1));
v___x_701_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_699_);
lean_ctor_set(v___x_701_, 2, v___x_698_);
return v___x_701_;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl(void){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lake_DSL_scriptDecl___closed__6, &l_Lake_DSL_scriptDecl___closed__6_once, _init_l_Lake_DSL_scriptDecl___closed__6);
return v___x_702_;
}
}
lean_object* runtime_initialize_Lake_DSL_DeclUtil(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
