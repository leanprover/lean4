// Lean compiler output
// Module: Lake.DSL.DeclUtil
// Imports: public import Lake.Util.Binder public import Lake.Config.MetaClasses public import Lean.Elab.Command
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
static const lean_string_object l_Lake_DSL_packageDeclName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_package"};
static const lean_object* l_Lake_DSL_packageDeclName___closed__0 = (const lean_object*)&l_Lake_DSL_packageDeclName___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lake_DSL_packageDeclName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 195, 71, 41, 5, 9, 150, 238)}};
static const lean_object* l_Lake_DSL_packageDeclName___closed__1 = (const lean_object*)&l_Lake_DSL_packageDeclName___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_packageDeclName = (const lean_object*)&l_Lake_DSL_packageDeclName___closed__1_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__0 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__1 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__2 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__3 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value_aux_2),((lean_object*)&l_Lake_DSL_expandAttrs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lake_DSL_expandAttrs___closed__4 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_DSL_expandAttrs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_DSL_expandAttrs___closed__5 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__5_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object*);
static const lean_string_object l_Lake_DSL_identOrStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identOrStr"};
static const lean_object* l_Lake_DSL_identOrStr___closed__0 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__0_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_DSL_identOrStr___closed__1 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__1_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_DSL_identOrStr___closed__2 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__3_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__3_value_aux_1),((lean_object*)&l_Lake_DSL_identOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 188, 128, 7, 103, 245, 245, 49)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__3 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__3_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lake_DSL_identOrStr___closed__4 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__4_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__5 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__5_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_DSL_identOrStr___closed__6 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__6_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__7 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__7_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__7_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__8 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__8_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lake_DSL_identOrStr___closed__9 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__9_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__10 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__10_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__10_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__11 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__11_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__5_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__11_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__12 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__12_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__0_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__12_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__13 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__13_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_identOrStr = (const lean_object*)&l_Lake_DSL_identOrStr___closed__13_value;
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
static const lean_string_object l_Lake_DSL_declField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declField"};
static const lean_object* l_Lake_DSL_declField___closed__0 = (const lean_object*)&l_Lake_DSL_declField___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declField___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 4, 47, 196, 245, 170, 224, 183)}};
static const lean_object* l_Lake_DSL_declField___closed__1 = (const lean_object*)&l_Lake_DSL_declField___closed__1_value;
static const lean_string_object l_Lake_DSL_declField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_DSL_declField___closed__2 = (const lean_object*)&l_Lake_DSL_declField___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declField___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_DSL_declField___closed__3 = (const lean_object*)&l_Lake_DSL_declField___closed__3_value;
static const lean_string_object l_Lake_DSL_declField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_DSL_declField___closed__4 = (const lean_object*)&l_Lake_DSL_declField___closed__4_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__4_value)}};
static const lean_object* l_Lake_DSL_declField___closed__5 = (const lean_object*)&l_Lake_DSL_declField___closed__5_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_declField___closed__5_value)}};
static const lean_object* l_Lake_DSL_declField___closed__6 = (const lean_object*)&l_Lake_DSL_declField___closed__6_value;
static const lean_string_object l_Lake_DSL_declField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_DSL_declField___closed__7 = (const lean_object*)&l_Lake_DSL_declField___closed__7_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declField___closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_DSL_declField___closed__8 = (const lean_object*)&l_Lake_DSL_declField___closed__8_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_DSL_declField___closed__9 = (const lean_object*)&l_Lake_DSL_declField___closed__9_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declField___closed__6_value),((lean_object*)&l_Lake_DSL_declField___closed__9_value)}};
static const lean_object* l_Lake_DSL_declField___closed__10 = (const lean_object*)&l_Lake_DSL_declField___closed__10_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__0_value),((lean_object*)&l_Lake_DSL_declField___closed__1_value),((lean_object*)&l_Lake_DSL_declField___closed__10_value)}};
static const lean_object* l_Lake_DSL_declField___closed__11 = (const lean_object*)&l_Lake_DSL_declField___closed__11_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declField = (const lean_object*)&l_Lake_DSL_declField___closed__11_value;
static const lean_string_object l_Lake_DSL_structVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structVal"};
static const lean_object* l_Lake_DSL_structVal___closed__0 = (const lean_object*)&l_Lake_DSL_structVal___closed__0_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_structVal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_structVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_structVal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 76, 221, 200, 37, 245, 130, 150)}};
static const lean_object* l_Lake_DSL_structVal___closed__1 = (const lean_object*)&l_Lake_DSL_structVal___closed__1_value;
static const lean_string_object l_Lake_DSL_structVal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lake_DSL_structVal___closed__2 = (const lean_object*)&l_Lake_DSL_structVal___closed__2_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__2_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__3 = (const lean_object*)&l_Lake_DSL_structVal___closed__3_value;
static const lean_string_object l_Lake_DSL_structVal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_DSL_structVal___closed__4 = (const lean_object*)&l_Lake_DSL_structVal___closed__4_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_structVal___closed__4_value),LEAN_SCALAR_PTR_LITERAL(176, 25, 16, 25, 82, 100, 240, 199)}};
static const lean_object* l_Lake_DSL_structVal___closed__5 = (const lean_object*)&l_Lake_DSL_structVal___closed__5_value;
static const lean_string_object l_Lake_DSL_structVal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sepByIndentSemicolon"};
static const lean_object* l_Lake_DSL_structVal___closed__6 = (const lean_object*)&l_Lake_DSL_structVal___closed__6_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_structVal___closed__6_value),LEAN_SCALAR_PTR_LITERAL(139, 141, 160, 225, 89, 107, 71, 117)}};
static const lean_object* l_Lake_DSL_structVal___closed__7 = (const lean_object*)&l_Lake_DSL_structVal___closed__7_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__7_value),((lean_object*)&l_Lake_DSL_declField___closed__11_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__8 = (const lean_object*)&l_Lake_DSL_structVal___closed__8_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__5_value),((lean_object*)&l_Lake_DSL_structVal___closed__8_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__9 = (const lean_object*)&l_Lake_DSL_structVal___closed__9_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__9_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__10 = (const lean_object*)&l_Lake_DSL_structVal___closed__10_value;
static const lean_string_object l_Lake_DSL_structVal___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lake_DSL_structVal___closed__11 = (const lean_object*)&l_Lake_DSL_structVal___closed__11_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__11_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__12 = (const lean_object*)&l_Lake_DSL_structVal___closed__12_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__10_value),((lean_object*)&l_Lake_DSL_structVal___closed__12_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__13 = (const lean_object*)&l_Lake_DSL_structVal___closed__13_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__0_value),((lean_object*)&l_Lake_DSL_structVal___closed__1_value),((lean_object*)&l_Lake_DSL_structVal___closed__13_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__14 = (const lean_object*)&l_Lake_DSL_structVal___closed__14_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_structVal = (const lean_object*)&l_Lake_DSL_structVal___closed__14_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declValDo"};
static const lean_object* l_Lake_DSL_declValDo___closed__0 = (const lean_object*)&l_Lake_DSL_declValDo___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declValDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 210, 120, 194, 116, 135, 247, 152)}};
static const lean_object* l_Lake_DSL_declValDo___closed__1 = (const lean_object*)&l_Lake_DSL_declValDo___closed__1_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lake_DSL_declValDo___closed__2 = (const lean_object*)&l_Lake_DSL_declValDo___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declValDo___closed__2_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lake_DSL_declValDo___closed__3 = (const lean_object*)&l_Lake_DSL_declValDo___closed__3_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__3_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__4 = (const lean_object*)&l_Lake_DSL_declValDo___closed__4_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lake_DSL_declValDo___closed__5 = (const lean_object*)&l_Lake_DSL_declValDo___closed__5_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value_aux_2),((lean_object*)&l_Lake_DSL_declValDo___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l_Lake_DSL_declValDo___closed__6 = (const lean_object*)&l_Lake_DSL_declValDo___closed__6_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__7 = (const lean_object*)&l_Lake_DSL_declValDo___closed__7_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValDo___closed__4_value),((lean_object*)&l_Lake_DSL_declValDo___closed__7_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__8 = (const lean_object*)&l_Lake_DSL_declValDo___closed__8_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lake_DSL_declValDo___closed__9 = (const lean_object*)&l_Lake_DSL_declValDo___closed__9_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declValDo___closed__9_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lake_DSL_declValDo___closed__10 = (const lean_object*)&l_Lake_DSL_declValDo___closed__10_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l_Lake_DSL_declValDo___closed__11 = (const lean_object*)&l_Lake_DSL_declValDo___closed__11_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value_aux_2),((lean_object*)&l_Lake_DSL_declValDo___closed__11_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l_Lake_DSL_declValDo___closed__12 = (const lean_object*)&l_Lake_DSL_declValDo___closed__12_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__13 = (const lean_object*)&l_Lake_DSL_declValDo___closed__13_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__10_value),((lean_object*)&l_Lake_DSL_declValDo___closed__13_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__14 = (const lean_object*)&l_Lake_DSL_declValDo___closed__14_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValDo___closed__8_value),((lean_object*)&l_Lake_DSL_declValDo___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__15 = (const lean_object*)&l_Lake_DSL_declValDo___closed__15_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__0_value),((lean_object*)&l_Lake_DSL_declValDo___closed__1_value),((lean_object*)&l_Lake_DSL_declValDo___closed__15_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__16 = (const lean_object*)&l_Lake_DSL_declValDo___closed__16_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declValDo = (const lean_object*)&l_Lake_DSL_declValDo___closed__16_value;
static const lean_string_object l_Lake_DSL_declValStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValStruct"};
static const lean_object* l_Lake_DSL_declValStruct___closed__0 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValStruct___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValStruct___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declValStruct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 214, 189, 204, 150, 4, 239, 13)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__1 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__1_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValDo___closed__4_value),((lean_object*)&l_Lake_DSL_structVal___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__2 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__2_value),((lean_object*)&l_Lake_DSL_declValDo___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__3 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__3_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declValStruct___closed__0_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__1_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__3_value)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__4 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declValStruct = (const lean_object*)&l_Lake_DSL_declValStruct___closed__4_value;
static const lean_string_object l_Lake_DSL_declValWhere___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declValWhere"};
static const lean_object* l_Lake_DSL_declValWhere___closed__0 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declValWhere___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 133, 86, 223, 245, 102, 246, 81)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__1 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__1_value;
static const lean_string_object l_Lake_DSL_declValWhere___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " where "};
static const lean_object* l_Lake_DSL_declValWhere___closed__2 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__2_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__3 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__3_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__9_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__4 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__4_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__4_value),((lean_object*)&l_Lake_DSL_declValDo___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__5 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__5_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__0_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__1_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__5_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__6 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__6_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declValWhere = (const lean_object*)&l_Lake_DSL_declValWhere___closed__6_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpleDeclSig"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__0 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__0_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 30, 135, 149, 186, 116, 70, 7)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__1 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__2 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__2_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value_aux_2),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__3 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__4 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__4_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__4_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__5 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__5_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__6 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__7 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__7_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value_aux_2),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__7_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__8 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__9 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__9_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__5_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__9_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__10 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__10_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__0_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__10_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__11 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__11_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_simpleDeclSig = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__11_value;
static const lean_string_object l_Lake_DSL_optConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_DSL_optConfig___closed__0 = (const lean_object*)&l_Lake_DSL_optConfig___closed__0_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_optConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_optConfig___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_optConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_optConfig___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_optConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_DSL_optConfig___closed__1 = (const lean_object*)&l_Lake_DSL_optConfig___closed__1_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__5_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__6_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__4_value)}};
static const lean_object* l_Lake_DSL_optConfig___closed__2 = (const lean_object*)&l_Lake_DSL_optConfig___closed__2_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__10_value),((lean_object*)&l_Lake_DSL_optConfig___closed__2_value)}};
static const lean_object* l_Lake_DSL_optConfig___closed__3 = (const lean_object*)&l_Lake_DSL_optConfig___closed__3_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_optConfig___closed__0_value),((lean_object*)&l_Lake_DSL_optConfig___closed__1_value),((lean_object*)&l_Lake_DSL_optConfig___closed__3_value)}};
static const lean_object* l_Lake_DSL_optConfig___closed__4 = (const lean_object*)&l_Lake_DSL_optConfig___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_optConfig = (const lean_object*)&l_Lake_DSL_optConfig___closed__4_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "bracketedSimpleBinder"};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__0 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 236, 129, 27, 124, 223, 134, 77)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__1 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__2 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__2_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__2_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__3 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__3_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__4 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__4_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__5 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__5_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__5_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__6 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__6_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__6_value),((lean_object*)&l_Lake_DSL_declField___closed__9_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__7 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__7_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__10_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__7_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__8 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__8_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__4_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__8_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__9 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__9_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__10 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__10_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__10_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__11 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__11_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__9_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__11_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__12 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__12_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__0_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__12_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__13 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__13_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_bracketedSimpleBinder = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__13_value;
static const lean_string_object l_Lake_DSL_simpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpleBinder"};
static const lean_object* l_Lake_DSL_simpleBinder___closed__0 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_simpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 16, 244, 231, 102, 138, 237, 36)}};
static const lean_object* l_Lake_DSL_simpleBinder___closed__1 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value;
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__5_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__13_value)}};
static const lean_object* l_Lake_DSL_simpleBinder___closed__2 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__2_value;
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleBinder___closed__0_value),((lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value),((lean_object*)&l_Lake_DSL_simpleBinder___closed__2_value)}};
static const lean_object* l_Lake_DSL_simpleBinder___closed__3 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_simpleBinder = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__3_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__0 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_2),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__1 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__2 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__2_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__3 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__3_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_2),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__4 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__5 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__5_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_2),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__6 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__7 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__7_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__8 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__8_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__9 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__9_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lake_DSL_expandOptSimpleBinder___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__10;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__11_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__11 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__11_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__11_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__12 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__12_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__13 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__14 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__14_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__15 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__16 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__16_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__17_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__17 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__17_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__17_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__18 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__18_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__19 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__19_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__19_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__20 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__20_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__21 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__21_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__18_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__21_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__22 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__22_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__16_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__22_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__23 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__23_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__14_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__23_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__24 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__24_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__12_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__24_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__25 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__25_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__26 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__26_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__27 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__27_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__27_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__28 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__28_value;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "ill-formed field declaration syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "redefined field '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "' ('"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "' is an alias of '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "')"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unknown '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "' field '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_2),((lean_object*)&l_Lake_DSL_structVal___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0 = (const lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1 = (const lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__28_value),((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value)}};
static const lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2 = (const lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2_value;
lean_object* l_Lean_Elab_Command_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_DSL_elabConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake_DSL_elabConfig___closed__0 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__0_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake_DSL_elabConfig___closed__1 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__1_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lake_DSL_elabConfig___closed__2 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__2_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lake_DSL_elabConfig___closed__3 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__3_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake_DSL_elabConfig___closed__4 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__4_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lake_DSL_elabConfig___closed__5 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__5_value;
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__6;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__7;
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_DSL_elabConfig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_elabConfig___closed__8 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__8_value;
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_DSL_elabConfig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_elabConfig___closed__9 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__9_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l_Lake_DSL_elabConfig___closed__10 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__10_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l_Lake_DSL_elabConfig___closed__11 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__11_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___closed__12_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___closed__12_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___closed__11_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l_Lake_DSL_elabConfig___closed__12 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__12_value;
extern lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
extern lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM;
extern lean_object* l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__13;
static const lean_string_object l_Lake_DSL_elabConfig___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed configuration syntax"};
static const lean_object* l_Lake_DSL_elabConfig___closed__14 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__14_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__15;
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM;
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_getMainModule___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__4));
lean_inc(x_2);
x_4 = l_Lean_Syntax_isOfKind(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
lean_dec(x_2);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = l_Lean_Syntax_TSepArray_getElems___redArg(x_8);
lean_dec_ref(x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lake_DSL_identOrStr___closed__3));
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = ((lean_object*)(l_Lake_DSL_identOrStr___closed__7));
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lake_DSL_identOrStr___closed__10));
lean_inc(x_6);
x_10 = l_Lean_Syntax_isOfKind(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_TSyntax_getString(x_6);
x_13 = lean_box(0);
x_14 = l_Lean_Name_str___override(x_13, x_12);
x_15 = l_Lean_mkIdentFrom(x_6, x_14, x_8);
lean_dec(x_6);
return x_15;
}
}
else
{
return x_6;
}
}
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__9));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 5);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = 0;
x_6 = l_Lean_SourceInfo_fromRef(x_4, x_5);
lean_dec(x_4);
x_7 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
x_8 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(x_6);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Syntax_node1(x_6, x_7, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_100; 
x_12 = lean_ctor_get(x_1, 0);
x_100 = !lean_is_exclusive(x_1);
if (x_100 == 0)
{
x_13 = x_1;
x_14 = x_100;
goto block_99;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l_Lake_DSL_simpleBinder___closed__1));
lean_inc(x_12);
x_16 = l_Lean_Syntax_isOfKind(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_del_object(x_13);
lean_dec(x_12);
x_17 = lean_ctor_get(x_2, 5);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = l_Lean_SourceInfo_fromRef(x_17, x_16);
lean_dec(x_17);
x_19 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
x_20 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Syntax_node1(x_18, x_19, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_12, x_24);
lean_dec(x_12);
x_26 = ((lean_object*)(l_Lake_DSL_identOrStr___closed__7));
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = ((lean_object*)(l_Lake_DSL_bracketedSimpleBinder___closed__1));
lean_inc(x_25);
x_29 = l_Lean_Syntax_isOfKind(x_25, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
lean_del_object(x_13);
x_30 = lean_ctor_get(x_2, 5);
lean_inc(x_30);
lean_dec_ref(x_2);
x_31 = l_Lean_SourceInfo_fromRef(x_30, x_27);
lean_dec(x_30);
x_32 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
x_33 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(x_31);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Syntax_node1(x_31, x_32, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = l_Lean_Syntax_getArg(x_25, x_37);
x_82 = lean_unsigned_to_nat(2u);
x_83 = l_Lean_Syntax_getArg(x_25, x_82);
lean_dec(x_25);
x_84 = l_Lean_Syntax_isNone(x_83);
if (x_84 == 0)
{
uint8_t x_85; 
lean_inc(x_83);
x_85 = l_Lean_Syntax_matchesNull(x_83, x_82);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_83);
lean_dec(x_38);
lean_del_object(x_13);
x_86 = lean_ctor_get(x_2, 5);
lean_inc(x_86);
lean_dec_ref(x_2);
x_87 = l_Lean_SourceInfo_fromRef(x_86, x_27);
lean_dec(x_86);
x_88 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
x_89 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(x_87);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Syntax_node1(x_87, x_88, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_Syntax_getArg(x_83, x_37);
lean_dec(x_83);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_93);
x_94 = x_13;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_93);
x_94 = x_96;
goto block_95;
}
block_95:
{
x_66 = x_94;
x_67 = x_2;
x_68 = x_3;
goto block_81;
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_83);
lean_del_object(x_13);
x_97 = lean_box(0);
x_66 = x_97;
x_67 = x_2;
x_68 = x_3;
goto block_81;
}
block_65:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_44 = l_Lean_SourceInfo_fromRef(x_42, x_27);
lean_dec(x_42);
x_45 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__4));
x_46 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__6));
x_47 = ((lean_object*)(l_Lake_DSL_bracketedSimpleBinder___closed__2));
lean_inc(x_44);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__8));
x_50 = lean_obj_once(&l_Lake_DSL_expandOptSimpleBinder___closed__10, &l_Lake_DSL_expandOptSimpleBinder___closed__10_once, _init_l_Lake_DSL_expandOptSimpleBinder___closed__10);
x_51 = lean_box(0);
x_52 = l_Lean_addMacroScope(x_40, x_51, x_41);
x_53 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__25));
lean_inc(x_44);
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
lean_inc(x_44);
x_55 = l_Lean_Syntax_node1(x_44, x_49, x_54);
lean_inc(x_44);
x_56 = l_Lean_Syntax_node2(x_44, x_46, x_48, x_55);
x_57 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__26));
lean_inc(x_44);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_57);
x_59 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
lean_inc(x_44);
x_60 = l_Lean_Syntax_node1(x_44, x_59, x_43);
x_61 = ((lean_object*)(l_Lake_DSL_bracketedSimpleBinder___closed__10));
lean_inc(x_44);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Syntax_node5(x_44, x_45, x_56, x_38, x_58, x_60, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_39);
return x_64;
}
block_81:
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 5);
lean_inc(x_71);
lean_dec_ref(x_67);
x_72 = l_Lean_SourceInfo_fromRef(x_71, x_27);
x_73 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(x_72);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
x_76 = l_Lean_Syntax_node1(x_72, x_75, x_74);
x_39 = x_68;
x_40 = x_69;
x_41 = x_70;
x_42 = x_71;
x_43 = x_76;
goto block_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_67, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_67, 5);
lean_inc(x_79);
lean_dec_ref(x_67);
x_80 = lean_ctor_get(x_66, 0);
lean_inc(x_80);
lean_dec_ref(x_66);
x_39 = x_68;
x_40 = x_77;
x_41 = x_78;
x_42 = x_79;
x_43 = x_80;
goto block_65;
}
}
}
}
else
{
lean_object* x_98; 
lean_del_object(x_13);
lean_dec_ref(x_2);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_25);
lean_ctor_set(x_98, 1, x_3);
return x_98;
}
}
}
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = l_Lean_SourceInfo_fromRef(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
x_2 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
x_3 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9));
x_2 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(x_1, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = 1;
x_13 = l_Lean_mkIdentFrom(x_10, x_4, x_12);
lean_dec(x_10);
x_14 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
x_15 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2));
x_16 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4));
x_17 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
x_18 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6);
x_19 = l_Lean_Syntax_node2(x_14, x_16, x_13, x_18);
x_20 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8));
x_21 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10);
x_22 = l_Lean_Syntax_node3(x_14, x_20, x_21, x_18, x_11);
x_23 = l_Lean_Syntax_node3(x_14, x_17, x_18, x_18, x_22);
x_24 = l_Lean_Syntax_node2(x_14, x_15, x_19, x_23);
x_25 = lean_array_push(x_9, x_24);
x_1 = x_25;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0));
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2);
x_12 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; uint8_t x_99; uint8_t x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_130; uint8_t x_143; 
x_125 = 2;
x_143 = l_Lean_instBEqMessageSeverity_beq(x_3, x_125);
if (x_143 == 0)
{
x_130 = x_143;
goto block_142;
}
else
{
uint8_t x_144; 
lean_inc_ref(x_2);
x_144 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_130 = x_144;
goto block_142;
}
block_70:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_53; 
x_19 = lean_ctor_get(x_18, 0);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
x_20 = x_18;
x_21 = x_53;
goto block_52;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_51; 
x_22 = lean_st_ref_take(x_15);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_19, 3);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 2);
x_28 = lean_ctor_get(x_22, 3);
x_29 = lean_ctor_get(x_22, 4);
x_30 = lean_ctor_get(x_22, 5);
x_31 = lean_ctor_get(x_22, 6);
x_32 = lean_ctor_get(x_22, 7);
x_33 = lean_ctor_get(x_22, 8);
x_34 = lean_ctor_get(x_22, 9);
x_35 = lean_ctor_get(x_22, 10);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
x_36 = x_22;
x_37 = x_51;
goto block_50;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
x_36 = lean_box(0);
x_37 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_12);
x_40 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_10);
lean_ctor_set(x_40, 2, x_13);
lean_ctor_set(x_40, 3, x_11);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 1, x_9);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 2, x_4);
x_41 = l_Lean_MessageLog_add(x_40, x_26);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_41);
x_42 = x_36;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_27);
lean_ctor_set(x_49, 3, x_28);
lean_ctor_set(x_49, 4, x_29);
lean_ctor_set(x_49, 5, x_30);
lean_ctor_set(x_49, 6, x_31);
lean_ctor_set(x_49, 7, x_32);
lean_ctor_set(x_49, 8, x_33);
lean_ctor_set(x_49, 9, x_34);
lean_ctor_set(x_49, 10, x_35);
x_42 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_st_ref_set(x_15, x_42);
x_44 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_44);
x_45 = x_20;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_54 = lean_ctor_get(x_18, 0);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
x_55 = x_18;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_62 = lean_ctor_get(x_16, 0);
x_69 = !lean_is_exclusive(x_16);
if (x_69 == 0)
{
x_63 = x_16;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_16);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
block_98:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_97; 
x_76 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_77);
x_78 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
lean_dec_ref(x_5);
x_79 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_80 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(x_79, x_6);
x_81 = lean_ctor_get(x_80, 0);
x_97 = !lean_is_exclusive(x_80);
if (x_97 == 0)
{
x_82 = x_80;
x_83 = x_97;
goto block_96;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc_ref(x_77);
x_84 = l_Lean_FileMap_toPosition(x_77, x_72);
lean_dec(x_72);
x_85 = l_Lean_FileMap_toPosition(x_77, x_75);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__9));
if (x_78 == 0)
{
lean_del_object(x_82);
x_8 = x_73;
x_9 = x_74;
x_10 = x_84;
x_11 = x_87;
x_12 = x_81;
x_13 = x_86;
x_14 = x_76;
x_15 = x_6;
goto block_70;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_box(x_71);
x_89 = lean_box(x_78);
x_90 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_89);
lean_inc(x_81);
x_91 = l_Lean_MessageData_hasTag(x_90, x_81);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_86);
lean_dec_ref(x_84);
lean_dec(x_81);
lean_dec_ref(x_76);
x_92 = lean_box(0);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_92);
x_93 = x_82;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
else
{
lean_del_object(x_82);
x_8 = x_73;
x_9 = x_74;
x_10 = x_84;
x_11 = x_87;
x_12 = x_81;
x_13 = x_86;
x_14 = x_76;
x_15 = x_6;
goto block_70;
}
}
}
}
block_106:
{
lean_object* x_104; 
x_104 = l_Lean_Syntax_getTailPos_x3f(x_101, x_100);
lean_dec(x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_inc(x_103);
x_71 = x_99;
x_72 = x_103;
x_73 = x_100;
x_74 = x_102;
x_75 = x_103;
goto block_98;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_71 = x_99;
x_72 = x_103;
x_73 = x_100;
x_74 = x_102;
x_75 = x_105;
goto block_98;
}
}
block_124:
{
lean_object* x_110; 
x_110 = l_Lean_Elab_Command_getRef___redArg(x_5);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = l_Lean_replaceRef(x_1, x_111);
lean_dec(x_111);
x_113 = l_Lean_Syntax_getPos_x3f(x_112, x_108);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_unsigned_to_nat(0u);
x_99 = x_107;
x_100 = x_108;
x_101 = x_112;
x_102 = x_109;
x_103 = x_114;
goto block_106;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec_ref(x_113);
x_99 = x_107;
x_100 = x_108;
x_101 = x_112;
x_102 = x_109;
x_103 = x_115;
goto block_106;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_116 = lean_ctor_get(x_110, 0);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
x_117 = x_110;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
block_129:
{
if (x_128 == 0)
{
x_107 = x_126;
x_108 = x_127;
x_109 = x_3;
goto block_124;
}
else
{
x_107 = x_126;
x_108 = x_127;
x_109 = x_125;
goto block_124;
}
}
block_142:
{
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; 
x_131 = lean_st_ref_get(x_6);
x_132 = lean_ctor_get(x_131, 2);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Elab_Command_instInhabitedScope_default;
x_134 = l_List_head_x21___redArg(x_133, x_132);
lean_dec(x_132);
x_135 = lean_ctor_get(x_134, 1);
lean_inc_ref(x_135);
lean_dec(x_134);
x_136 = 1;
x_137 = l_Lean_instBEqMessageSeverity_beq(x_3, x_136);
if (x_137 == 0)
{
lean_dec_ref(x_135);
x_126 = x_130;
x_127 = x_130;
x_128 = x_137;
goto block_129;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = l_Lean_warningAsError;
x_139 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(x_135, x_138);
lean_dec_ref(x_135);
x_126 = x_130;
x_127 = x_130;
x_128 = x_139;
goto block_129;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = 0;
x_8 = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(x_1, x_2, x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 8);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_dec_ref(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_42; 
x_9 = lean_st_ref_take(x_2);
x_10 = lean_ctor_get(x_9, 8);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 5);
x_17 = lean_ctor_get(x_9, 6);
x_18 = lean_ctor_get(x_9, 7);
x_19 = lean_ctor_get(x_9, 9);
x_20 = lean_ctor_get(x_9, 10);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
x_21 = x_9;
x_22 = x_42;
goto block_41;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_10);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = x_42;
goto block_41;
}
block_41:
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_40; 
x_23 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 2);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
x_27 = x_10;
x_28 = x_40;
goto block_39;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_PersistentArray_push___redArg(x_26, x_1);
if (x_28 == 0)
{
lean_ctor_set(x_27, 2, x_29);
x_30 = x_27;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_23);
x_30 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_31; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 8, x_30);
x_31 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_12);
lean_ctor_set(x_36, 2, x_13);
lean_ctor_set(x_36, 3, x_14);
lean_ctor_set(x_36, 4, x_15);
lean_ctor_set(x_36, 5, x_16);
lean_ctor_set(x_36, 6, x_17);
lean_ctor_set(x_36, 7, x_18);
lean_ctor_set(x_36, 8, x_30);
lean_ctor_set(x_36, 9, x_19);
lean_ctor_set(x_36, 10, x_20);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_st_ref_set(x_2, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec_ref(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(x_11, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_5 = x_2;
x_6 = x_26;
goto block_25;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
x_11 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = l_Lean_indentD(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_30; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_16 = x_14;
x_17 = x_30;
goto block_29;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_1);
x_19 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_18);
x_19 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofSyntax(x_15);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(x_24, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(x_9, x_7, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_5, 0);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_22 = x_5;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_5);
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
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 8);
x_16 = lean_ctor_get(x_3, 9);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_3, 7);
lean_dec(x_27);
x_18 = x_3;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_ctor_set(x_18, 7, x_20);
x_21 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_10);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_12);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_14);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_17);
x_21 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_22; 
x_22 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(x_2, x_21, x_4);
return x_22;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_6, 0);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_29 = x_6;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
x_3 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_7);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_array_uget_borrowed(x_3, x_5);
x_18 = ((lean_object*)(l_Lake_DSL_declField___closed__1));
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1);
lean_inc_ref(x_7);
x_21 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(x_17, x_20, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
x_10 = x_6;
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
x_23 = x_21;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Syntax_getArg(x_17, x_30);
x_32 = l_Lean_TSyntax_getId(x_31);
lean_inc(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4);
lean_inc(x_1);
lean_inc(x_17);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_1);
x_36 = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(x_35, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec_ref(x_36);
x_37 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_2, x_32);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(2u);
x_42 = l_Lean_Syntax_getArg(x_17, x_41);
if (x_40 == 0)
{
if (x_19 == 0)
{
lean_dec(x_32);
goto block_45;
}
else
{
uint8_t x_46; 
x_46 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_39, x_6);
if (x_46 == 0)
{
lean_dec(x_32);
goto block_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6);
lean_inc(x_39);
x_48 = l_Lean_MessageData_ofName(x_39);
lean_inc_ref(x_48);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofName(x_32);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
x_57 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_inc_ref(x_7);
x_59 = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(x_31, x_58, x_7, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
goto block_45;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_31);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_59, 0);
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
x_61 = x_59;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
}
else
{
lean_dec(x_32);
goto block_45;
}
block_45:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_39, x_43, x_6);
x_10 = x_44;
goto block_14;
}
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_37);
x_68 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14);
x_69 = 0;
lean_inc(x_1);
x_70 = l_Lean_MessageData_ofConstName(x_1, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_MessageData_ofName(x_32);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc_ref(x_7);
x_78 = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(x_31, x_77, x_7, x_8);
lean_dec(x_31);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
x_10 = x_6;
goto block_14;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_79 = lean_ctor_get(x_78, 0);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
x_80 = x_78;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_87 = lean_ctor_get(x_36, 0);
x_94 = !lean_is_exclusive(x_36);
if (x_94 == 0)
{
x_88 = x_36;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_36);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_box(1);
x_8 = lean_array_size(x_3);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(x_1, x_2, x_3, x_8, x_9, x_7, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_29; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
x_13 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_15 = x_13;
x_16 = x_29;
goto block_28;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
x_18 = lean_box(2);
x_19 = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2));
x_20 = l_Lean_Syntax_mkSep(x_14, x_19);
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_array_push(x_22, x_20);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_23);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_24);
x_25 = x_15;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
x_30 = lean_ctor_get(x_10, 0);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
x_31 = x_10;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_25; 
x_25 = lean_ctor_get(x_2, 5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(x_3);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_5 = x_27;
goto block_24;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_5 = x_28;
goto block_24;
}
block_24:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_2);
lean_dec_ref(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
x_8 = x_6;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_addMacroScope(x_5, x_1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_ctor_get(x_6, 0);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
x_17 = x_6;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2));
x_5 = l_Lean_Elab_Command_withFreshMacroScope___redArg(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
x_8 = x_6;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_mkIdentFrom(x_1, x_7, x_2);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_6, 0);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
x_17 = x_6;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(x_1, x_6, x_3, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = 0;
x_8 = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(x_6, x_7, x_2, x_3);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_5, 0);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
x_10 = x_5;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_25; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_18 = x_1;
x_19 = x_25;
goto block_24;
}
else
{
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lake_DSL_expandIdentOrStrAsIdent(x_17);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_20);
x_21 = x_18;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_DSL_mkConfigDeclIdent(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__6(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__6, &l_Lake_DSL_elabConfig___closed__6_once, _init_l_Lake_DSL_elabConfig___closed__6);
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
x_2 = l_Lean_Elab_Command_instMonadRefCommandElabM;
x_3 = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_293; 
x_166 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
x_167 = lean_ctor_get(x_166, 0);
x_293 = !lean_is_exclusive(x_166);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_166, 1);
lean_dec(x_294);
x_168 = x_166;
x_169 = x_293;
goto block_292;
}
else
{
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_box(0);
x_169 = x_293;
goto block_292;
}
block_52:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_17 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__0));
lean_inc_ref(x_14);
lean_inc_ref(x_9);
lean_inc_ref(x_12);
x_18 = l_Lean_Name_mkStr4(x_12, x_9, x_14, x_17);
x_19 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__1));
lean_inc_ref(x_14);
lean_inc_ref(x_9);
lean_inc_ref(x_12);
x_20 = l_Lean_Name_mkStr4(x_12, x_9, x_14, x_19);
x_21 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
x_22 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
lean_inc(x_11);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc_ref_n(x_23, 7);
lean_inc(x_11);
x_24 = l_Lean_Syntax_node7(x_11, x_20, x_23, x_23, x_23, x_23, x_23, x_23, x_23);
x_25 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__2));
lean_inc_ref(x_14);
lean_inc_ref(x_9);
lean_inc_ref(x_12);
x_26 = l_Lean_Name_mkStr4(x_12, x_9, x_14, x_25);
x_27 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__3));
lean_inc(x_11);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
x_29 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__4));
lean_inc_ref(x_14);
lean_inc_ref(x_9);
lean_inc_ref(x_12);
x_30 = l_Lean_Name_mkStr4(x_12, x_9, x_14, x_29);
x_31 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
lean_inc(x_13);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_3);
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_36);
x_38 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__5));
lean_inc_ref(x_9);
lean_inc_ref(x_12);
x_39 = l_Lean_Name_mkStr4(x_12, x_9, x_14, x_38);
x_40 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__2));
x_41 = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__2));
x_42 = l_Lean_Name_mkStr4(x_12, x_9, x_40, x_41);
x_43 = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__26));
lean_inc(x_11);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_11);
x_45 = l_Lean_Syntax_node2(x_11, x_42, x_44, x_4);
lean_inc(x_11);
x_46 = l_Lean_Syntax_node1(x_11, x_21, x_45);
lean_inc_ref(x_23);
lean_inc(x_11);
x_47 = l_Lean_Syntax_node2(x_11, x_39, x_23, x_46);
lean_inc(x_11);
x_48 = l_Lean_Syntax_node5(x_11, x_26, x_28, x_37, x_47, x_15, x_23);
x_49 = l_Lean_Syntax_node2(x_11, x_18, x_24, x_48);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Command_withMacroExpansion___redArg(x_5, x_49, x_50, x_16, x_10);
return x_51;
}
block_133:
{
lean_object* x_62; 
x_62 = l_Lean_Elab_Command_getRef___redArg(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_115; 
lean_dec_ref(x_64);
x_65 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
x_66 = lean_ctor_get(x_65, 0);
x_115 = !lean_is_exclusive(x_65);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_65, 1);
lean_dec(x_116);
x_67 = x_65;
x_68 = x_115;
goto block_114;
}
else
{
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_box(0);
x_68 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_112; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_66, 2);
x_71 = lean_ctor_get(x_66, 3);
x_72 = lean_ctor_get(x_66, 4);
x_112 = !lean_is_exclusive(x_66);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_66, 1);
lean_dec(x_113);
x_73 = x_66;
x_74 = x_112;
goto block_111;
}
else
{
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_66);
x_73 = lean_box(0);
x_74 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
x_76 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref(x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_77, 0, x_69);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_78, 0, x_69);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_72);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_81, 0, x_71);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_82, 0, x_70);
if (x_74 == 0)
{
lean_ctor_set(x_73, 4, x_80);
lean_ctor_set(x_73, 3, x_81);
lean_ctor_set(x_73, 2, x_82);
lean_ctor_set(x_73, 1, x_75);
lean_ctor_set(x_73, 0, x_79);
x_83 = x_73;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_79);
lean_ctor_set(x_110, 1, x_75);
lean_ctor_set(x_110, 2, x_82);
lean_ctor_set(x_110, 3, x_81);
lean_ctor_set(x_110, 4, x_80);
x_83 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_84; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 1, x_76);
lean_ctor_set(x_67, 0, x_83);
x_84 = x_67;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_83);
lean_ctor_set(x_108, 1, x_76);
x_84 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_85 = l_Lean_Elab_Command_instMonadEnvCommandElabM;
x_86 = lean_ctor_get(x_60, 5);
x_87 = l_Lean_mkOptionalNode(x_61);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_mk_empty_array_with_capacity(x_88);
x_90 = lean_array_push(x_89, x_59);
x_91 = lean_array_push(x_90, x_57);
x_92 = lean_array_push(x_91, x_87);
x_93 = lean_box(2);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_56);
lean_ctor_set(x_94, 2, x_92);
x_95 = 0;
x_96 = l_Lean_SourceInfo_fromRef(x_63, x_95);
lean_dec(x_63);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Lean_getMainModule___redArg(x_84, x_85);
lean_inc(x_54);
lean_inc_ref(x_60);
x_98 = lean_apply_3(x_97, x_60, x_54, lean_box(0));
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_9 = x_53;
x_10 = x_54;
x_11 = x_96;
x_12 = x_55;
x_13 = x_93;
x_14 = x_58;
x_15 = x_94;
x_16 = x_60;
goto block_52;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_60);
lean_dec_ref(x_58);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_ctor_get(x_98, 0);
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
x_100 = x_98;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
else
{
lean_dec_ref(x_84);
x_9 = x_53;
x_10 = x_54;
x_11 = x_96;
x_12 = x_55;
x_13 = x_93;
x_14 = x_58;
x_15 = x_94;
x_16 = x_60;
goto block_52;
}
}
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_124; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_64, 0);
x_124 = !lean_is_exclusive(x_64);
if (x_124 == 0)
{
x_118 = x_64;
x_119 = x_124;
goto block_123;
}
else
{
lean_inc(x_117);
lean_dec(x_64);
x_118 = lean_box(0);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_119 == 0)
{
x_120 = x_118;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_117);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_62, 0);
x_132 = !lean_is_exclusive(x_62);
if (x_132 == 0)
{
x_126 = x_62;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_62);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
block_165:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_137);
x_140 = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(x_1, x_139, x_135, x_137, x_138);
lean_dec_ref(x_135);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__10));
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_134);
lean_ctor_set(x_143, 1, x_142);
x_144 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__0));
x_145 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__1));
x_146 = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__6));
x_147 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__12));
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_148; 
x_148 = lean_box(0);
x_53 = x_145;
x_54 = x_138;
x_55 = x_144;
x_56 = x_147;
x_57 = x_141;
x_58 = x_146;
x_59 = x_143;
x_60 = x_137;
x_61 = x_148;
goto block_133;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_156; 
x_149 = lean_ctor_get(x_136, 0);
x_156 = !lean_is_exclusive(x_136);
if (x_156 == 0)
{
x_150 = x_136;
x_151 = x_156;
goto block_155;
}
else
{
lean_inc(x_149);
lean_dec(x_136);
x_150 = lean_box(0);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_151 == 0)
{
x_152 = x_150;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_149);
x_152 = x_154;
goto block_153;
}
block_153:
{
x_53 = x_145;
x_54 = x_138;
x_55 = x_144;
x_56 = x_147;
x_57 = x_141;
x_58 = x_146;
x_59 = x_143;
x_60 = x_137;
x_61 = x_152;
goto block_133;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_164; 
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_140, 0);
x_164 = !lean_is_exclusive(x_140);
if (x_164 == 0)
{
x_158 = x_140;
x_159 = x_164;
goto block_163;
}
else
{
lean_inc(x_157);
lean_dec(x_140);
x_158 = lean_box(0);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_159 == 0)
{
x_160 = x_158;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_157);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
block_292:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_290; 
x_170 = lean_ctor_get(x_167, 0);
x_171 = lean_ctor_get(x_167, 2);
x_172 = lean_ctor_get(x_167, 3);
x_173 = lean_ctor_get(x_167, 4);
x_290 = !lean_is_exclusive(x_167);
if (x_290 == 0)
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_167, 1);
lean_dec(x_291);
x_174 = x_167;
x_175 = x_290;
goto block_289;
}
else
{
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_167);
x_174 = lean_box(0);
x_175 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_176 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
x_177 = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref(x_170);
x_178 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_178, 0, x_170);
x_179 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_179, 0, x_170);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_181, 0, x_173);
x_182 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_182, 0, x_172);
x_183 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_183, 0, x_171);
if (x_175 == 0)
{
lean_ctor_set(x_174, 4, x_181);
lean_ctor_set(x_174, 3, x_182);
lean_ctor_set(x_174, 2, x_183);
lean_ctor_set(x_174, 1, x_176);
lean_ctor_set(x_174, 0, x_180);
x_184 = x_174;
goto block_287;
}
else
{
lean_object* x_288; 
x_288 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_288, 0, x_180);
lean_ctor_set(x_288, 1, x_176);
lean_ctor_set(x_288, 2, x_183);
lean_ctor_set(x_288, 3, x_182);
lean_ctor_set(x_288, 4, x_181);
x_184 = x_288;
goto block_287;
}
block_287:
{
lean_object* x_185; 
if (x_169 == 0)
{
lean_ctor_set(x_168, 1, x_177);
lean_ctor_set(x_168, 0, x_184);
x_185 = x_168;
goto block_285;
}
else
{
lean_object* x_286; 
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_184);
lean_ctor_set(x_286, 1, x_177);
x_185 = x_286;
goto block_285;
}
block_285:
{
lean_object* x_186; uint8_t x_187; 
x_186 = ((lean_object*)(l_Lake_DSL_optConfig___closed__1));
lean_inc(x_5);
x_187 = l_Lean_Syntax_isOfKind(x_5, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_188 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_189 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_190 = l_Lean_throwErrorAt___redArg(x_185, x_188, x_5, x_189);
x_191 = lean_apply_3(x_190, x_6, x_7, lean_box(0));
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_unsigned_to_nat(0u);
x_193 = l_Lean_Syntax_getArg(x_5, x_192);
lean_inc(x_193);
x_194 = l_Lean_Syntax_matchesNull(x_193, x_192);
if (x_194 == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_unsigned_to_nat(1u);
lean_inc(x_193);
x_196 = l_Lean_Syntax_matchesNull(x_193, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_193);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_197 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_198 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_199 = l_Lean_throwErrorAt___redArg(x_185, x_197, x_5, x_198);
x_200 = lean_apply_3(x_199, x_6, x_7, lean_box(0));
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = l_Lean_Syntax_getArg(x_193, x_192);
lean_dec(x_193);
x_202 = ((lean_object*)(l_Lake_DSL_declValWhere___closed__1));
lean_inc(x_201);
x_203 = l_Lean_Syntax_isOfKind(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = ((lean_object*)(l_Lake_DSL_declValStruct___closed__1));
lean_inc(x_201);
x_205 = l_Lean_Syntax_isOfKind(x_201, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_201);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_206 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_207 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_208 = l_Lean_throwErrorAt___redArg(x_185, x_206, x_5, x_207);
x_209 = lean_apply_3(x_208, x_6, x_7, lean_box(0));
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = l_Lean_Syntax_getArg(x_201, x_192);
x_211 = ((lean_object*)(l_Lake_DSL_structVal___closed__1));
lean_inc(x_210);
x_212 = l_Lean_Syntax_isOfKind(x_210, x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_213 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_214 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_215 = l_Lean_throwErrorAt___redArg(x_185, x_213, x_5, x_214);
x_216 = lean_apply_3(x_215, x_6, x_7, lean_box(0));
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = l_Lean_Syntax_getArg(x_210, x_195);
x_218 = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(x_217);
x_219 = l_Lean_Syntax_isOfKind(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_217);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_220 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_221 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_222 = l_Lean_throwErrorAt___redArg(x_185, x_220, x_5, x_221);
x_223 = lean_apply_3(x_222, x_6, x_7, lean_box(0));
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_233; uint8_t x_234; 
x_224 = l_Lean_Syntax_getArg(x_210, x_192);
lean_dec(x_210);
x_225 = l_Lean_Syntax_getArg(x_217, x_192);
lean_dec(x_217);
x_233 = l_Lean_Syntax_getArg(x_201, x_195);
lean_dec(x_201);
x_234 = l_Lean_Syntax_isNone(x_233);
if (x_234 == 0)
{
uint8_t x_235; 
lean_inc(x_233);
x_235 = l_Lean_Syntax_matchesNull(x_233, x_195);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_233);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_236 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_237 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_238 = l_Lean_throwErrorAt___redArg(x_185, x_236, x_5, x_237);
x_239 = lean_apply_3(x_238, x_6, x_7, lean_box(0));
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_240 = l_Lean_Syntax_getArg(x_233, x_192);
lean_dec(x_233);
x_241 = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(x_240);
x_242 = l_Lean_Syntax_isOfKind(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_240);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_243 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_244 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_245 = l_Lean_throwErrorAt___redArg(x_185, x_243, x_5, x_244);
x_246 = lean_apply_3(x_245, x_6, x_7, lean_box(0));
return x_246;
}
else
{
lean_object* x_247; 
lean_dec_ref(x_185);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_240);
x_226 = x_247;
x_227 = x_6;
x_228 = x_7;
goto block_232;
}
}
}
else
{
lean_object* x_248; 
lean_dec(x_233);
lean_dec_ref(x_185);
x_248 = lean_box(0);
x_226 = x_248;
x_227 = x_6;
x_228 = x_7;
goto block_232;
}
block_232:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = l_Lean_Syntax_getArgs(x_225);
lean_dec(x_225);
x_230 = l_Lean_Syntax_getHeadInfo(x_224);
lean_dec(x_224);
x_231 = l_Lean_Syntax_TSepArray_getElems___redArg(x_229);
lean_dec_ref(x_229);
x_134 = x_230;
x_135 = x_231;
x_136 = x_226;
x_137 = x_227;
x_138 = x_228;
goto block_165;
}
}
}
}
}
else
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_249 = l_Lean_Syntax_getArg(x_201, x_195);
x_250 = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(x_249);
x_251 = l_Lean_Syntax_isOfKind(x_249, x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_249);
lean_dec(x_201);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_252 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_253 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_254 = l_Lean_throwErrorAt___redArg(x_185, x_252, x_5, x_253);
x_255 = lean_apply_3(x_254, x_6, x_7, lean_box(0));
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_256 = l_Lean_Syntax_getArg(x_201, x_192);
x_257 = l_Lean_Syntax_getArg(x_249, x_192);
lean_dec(x_249);
x_265 = lean_unsigned_to_nat(2u);
x_266 = l_Lean_Syntax_getArg(x_201, x_265);
lean_dec(x_201);
x_267 = l_Lean_Syntax_isNone(x_266);
if (x_267 == 0)
{
uint8_t x_268; 
lean_inc(x_266);
x_268 = l_Lean_Syntax_matchesNull(x_266, x_195);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_266);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_269 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_270 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_271 = l_Lean_throwErrorAt___redArg(x_185, x_269, x_5, x_270);
x_272 = lean_apply_3(x_271, x_6, x_7, lean_box(0));
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = l_Lean_Syntax_getArg(x_266, x_192);
lean_dec(x_266);
x_274 = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(x_273);
x_275 = l_Lean_Syntax_isOfKind(x_273, x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_273);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_276 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
x_277 = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
x_278 = l_Lean_throwErrorAt___redArg(x_185, x_276, x_5, x_277);
x_279 = lean_apply_3(x_278, x_6, x_7, lean_box(0));
return x_279;
}
else
{
lean_object* x_280; 
lean_dec_ref(x_185);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_273);
x_258 = x_280;
x_259 = x_6;
x_260 = x_7;
goto block_264;
}
}
}
else
{
lean_object* x_281; 
lean_dec(x_266);
lean_dec_ref(x_185);
x_281 = lean_box(0);
x_258 = x_281;
x_259 = x_6;
x_260 = x_7;
goto block_264;
}
block_264:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = l_Lean_Syntax_getArgs(x_257);
lean_dec(x_257);
x_262 = l_Lean_Syntax_getHeadInfo(x_256);
lean_dec(x_256);
x_263 = l_Lean_Syntax_TSepArray_getElems___redArg(x_261);
lean_dec_ref(x_261);
x_134 = x_262;
x_135 = x_263;
x_136 = x_258;
x_137 = x_259;
x_138 = x_260;
goto block_165;
}
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_193);
lean_dec_ref(x_185);
x_282 = lean_box(2);
x_283 = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
x_284 = lean_box(0);
x_134 = x_282;
x_135 = x_283;
x_136 = x_284;
x_137 = x_6;
x_138 = x_7;
goto block_165;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_DSL_elabConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_9;
}
}
lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Binder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Binder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_MetaClasses(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_DeclUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_DeclUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_DeclUtil(builtin);
}
#ifdef __cplusplus
}
#endif
