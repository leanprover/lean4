// Lean compiler output
// Module: Lean.Data.Json.Elab
// Imports: public import Lean.Data.Json.FromToJson public meta import Lean.Syntax
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_json_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Json_json_quot___closed__0 = (const lean_object*)&l_Lean_Json_json_quot___closed__0_value;
static const lean_string_object l_Lean_Json_json_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Json_json_quot___closed__1 = (const lean_object*)&l_Lean_Json_json_quot___closed__1_value;
static const lean_string_object l_Lean_Json_json_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Json_json_quot___closed__2 = (const lean_object*)&l_Lean_Json_json_quot___closed__2_value;
static const lean_string_object l_Lean_Json_json_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Json_json_quot___closed__3 = (const lean_object*)&l_Lean_Json_json_quot___closed__3_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_json_quot___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Json_json_quot___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__4_value_aux_1),((lean_object*)&l_Lean_Json_json_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Json_json_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__4_value_aux_2),((lean_object*)&l_Lean_Json_json_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Json_json_quot___closed__4 = (const lean_object*)&l_Lean_Json_json_quot___closed__4_value;
static const lean_string_object l_Lean_Json_json_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "json"};
static const lean_object* l_Lean_Json_json_quot___closed__5 = (const lean_object*)&l_Lean_Json_json_quot___closed__5_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 242, 190, 241, 110, 39, 195, 20)}};
static const lean_ctor_object l_Lean_Json_json_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__6_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 235, 101, 110, 98, 158, 24, 121)}};
static const lean_object* l_Lean_Json_json_quot___closed__6 = (const lean_object*)&l_Lean_Json_json_quot___closed__6_value;
static const lean_string_object l_Lean_Json_json_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Json_json_quot___closed__7 = (const lean_object*)&l_Lean_Json_json_quot___closed__7_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Json_json_quot___closed__8 = (const lean_object*)&l_Lean_Json_json_quot___closed__8_value;
static const lean_string_object l_Lean_Json_json_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`(json| "};
static const lean_object* l_Lean_Json_json_quot___closed__9 = (const lean_object*)&l_Lean_Json_json_quot___closed__9_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__9_value)}};
static const lean_object* l_Lean_Json_json_quot___closed__10 = (const lean_object*)&l_Lean_Json_json_quot___closed__10_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 242, 190, 241, 110, 39, 195, 20)}};
static const lean_object* l_Lean_Json_json_quot___closed__11 = (const lean_object*)&l_Lean_Json_json_quot___closed__11_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json_json_quot___closed__12 = (const lean_object*)&l_Lean_Json_json_quot___closed__12_value;
static const lean_string_object l_Lean_Json_json_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Json_json_quot___closed__13 = (const lean_object*)&l_Lean_Json_json_quot___closed__13_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__13_value)}};
static const lean_object* l_Lean_Json_json_quot___closed__14 = (const lean_object*)&l_Lean_Json_json_quot___closed__14_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_quot___closed__12_value),((lean_object*)&l_Lean_Json_json_quot___closed__14_value)}};
static const lean_object* l_Lean_Json_json_quot___closed__15 = (const lean_object*)&l_Lean_Json_json_quot___closed__15_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_quot___closed__10_value),((lean_object*)&l_Lean_Json_json_quot___closed__15_value)}};
static const lean_object* l_Lean_Json_json_quot___closed__16 = (const lean_object*)&l_Lean_Json_json_quot___closed__16_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__6_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__16_value)}};
static const lean_object* l_Lean_Json_json_quot___closed__17 = (const lean_object*)&l_Lean_Json_json_quot___closed__17_value;
static const lean_ctor_object l_Lean_Json_json_quot___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__17_value)}};
static const lean_object* l_Lean_Json_json_quot___closed__18 = (const lean_object*)&l_Lean_Json_json_quot___closed__18_value;
LEAN_EXPORT const lean_object* l_Lean_Json_json_quot = (const lean_object*)&l_Lean_Json_json_quot___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_json;
static const lean_string_object l_Lean_Json_jsonNull___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Json"};
static const lean_object* l_Lean_Json_jsonNull___closed__0 = (const lean_object*)&l_Lean_Json_jsonNull___closed__0_value;
static const lean_string_object l_Lean_Json_jsonNull___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "jsonNull"};
static const lean_object* l_Lean_Json_jsonNull___closed__1 = (const lean_object*)&l_Lean_Json_jsonNull___closed__1_value;
static const lean_ctor_object l_Lean_Json_jsonNull___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_jsonNull___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonNull___closed__2_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_jsonNull___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonNull___closed__2_value_aux_1),((lean_object*)&l_Lean_Json_jsonNull___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 60, 51, 96, 46, 237, 101, 89)}};
static const lean_object* l_Lean_Json_jsonNull___closed__2 = (const lean_object*)&l_Lean_Json_jsonNull___closed__2_value;
static const lean_string_object l_Lean_Json_jsonNull___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Json_jsonNull___closed__3 = (const lean_object*)&l_Lean_Json_jsonNull___closed__3_value;
static const lean_ctor_object l_Lean_Json_jsonNull___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Json_jsonNull___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_jsonNull___closed__4 = (const lean_object*)&l_Lean_Json_jsonNull___closed__4_value;
static const lean_ctor_object l_Lean_Json_jsonNull___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_jsonNull___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Json_jsonNull___closed__4_value)}};
static const lean_object* l_Lean_Json_jsonNull___closed__5 = (const lean_object*)&l_Lean_Json_jsonNull___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Json_jsonNull = (const lean_object*)&l_Lean_Json_jsonNull___closed__5_value;
static const lean_string_object l_Lean_Json_jsonTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "jsonTrue"};
static const lean_object* l_Lean_Json_jsonTrue___closed__0 = (const lean_object*)&l_Lean_Json_jsonTrue___closed__0_value;
static const lean_ctor_object l_Lean_Json_jsonTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_jsonTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonTrue___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_jsonTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonTrue___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_jsonTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 223, 195, 247, 111, 22, 172, 54)}};
static const lean_object* l_Lean_Json_jsonTrue___closed__1 = (const lean_object*)&l_Lean_Json_jsonTrue___closed__1_value;
static const lean_string_object l_Lean_Json_jsonTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Json_jsonTrue___closed__2 = (const lean_object*)&l_Lean_Json_jsonTrue___closed__2_value;
static const lean_ctor_object l_Lean_Json_jsonTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Json_jsonTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_jsonTrue___closed__3 = (const lean_object*)&l_Lean_Json_jsonTrue___closed__3_value;
static const lean_ctor_object l_Lean_Json_jsonTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_jsonTrue___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Json_jsonTrue___closed__3_value)}};
static const lean_object* l_Lean_Json_jsonTrue___closed__4 = (const lean_object*)&l_Lean_Json_jsonTrue___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Json_jsonTrue = (const lean_object*)&l_Lean_Json_jsonTrue___closed__4_value;
static const lean_string_object l_Lean_Json_jsonFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "jsonFalse"};
static const lean_object* l_Lean_Json_jsonFalse___closed__0 = (const lean_object*)&l_Lean_Json_jsonFalse___closed__0_value;
static const lean_ctor_object l_Lean_Json_jsonFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_jsonFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_jsonFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_jsonFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 28, 34, 242, 49, 61, 87, 232)}};
static const lean_object* l_Lean_Json_jsonFalse___closed__1 = (const lean_object*)&l_Lean_Json_jsonFalse___closed__1_value;
static const lean_string_object l_Lean_Json_jsonFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Json_jsonFalse___closed__2 = (const lean_object*)&l_Lean_Json_jsonFalse___closed__2_value;
static const lean_ctor_object l_Lean_Json_jsonFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Json_jsonFalse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_jsonFalse___closed__3 = (const lean_object*)&l_Lean_Json_jsonFalse___closed__3_value;
static const lean_ctor_object l_Lean_Json_jsonFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_jsonFalse___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Json_jsonFalse___closed__3_value)}};
static const lean_object* l_Lean_Json_jsonFalse___closed__4 = (const lean_object*)&l_Lean_Json_jsonFalse___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Json_jsonFalse = (const lean_object*)&l_Lean_Json_jsonFalse___closed__4_value;
static const lean_string_object l_Lean_Json_json___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "json_"};
static const lean_object* l_Lean_Json_json___00__closed__0 = (const lean_object*)&l_Lean_Json_json___00__closed__0_value;
static const lean_ctor_object l_Lean_Json_json___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_json___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_json___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Json_json___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 121, 188, 241, 213, 216, 202, 40)}};
static const lean_object* l_Lean_Json_json___00__closed__1 = (const lean_object*)&l_Lean_Json_json___00__closed__1_value;
static const lean_string_object l_Lean_Json_json___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Json_json___00__closed__2 = (const lean_object*)&l_Lean_Json_json___00__closed__2_value;
static const lean_ctor_object l_Lean_Json_json___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Json_json___00__closed__3 = (const lean_object*)&l_Lean_Json_json___00__closed__3_value;
static const lean_ctor_object l_Lean_Json_json___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_json___00__closed__3_value)}};
static const lean_object* l_Lean_Json_json___00__closed__4 = (const lean_object*)&l_Lean_Json_json___00__closed__4_value;
static const lean_ctor_object l_Lean_Json_json___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_json___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Json_json___00__closed__4_value)}};
static const lean_object* l_Lean_Json_json___00__closed__5 = (const lean_object*)&l_Lean_Json_json___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Json_json__ = (const lean_object*)&l_Lean_Json_json___00__closed__5_value;
static const lean_string_object l_Lean_Json_json_x2d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "json-_"};
static const lean_object* l_Lean_Json_json_x2d___00__closed__0 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__0_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Json_json_x2d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 118, 11, 235, 35, 246, 227, 21)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__1 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__1_value;
static const lean_string_object l_Lean_Json_json_x2d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Json_json_x2d___00__closed__2 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__2_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_x2d___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__3 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__3_value;
static const lean_string_object l_Lean_Json_json_x2d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Json_json_x2d___00__closed__4 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__4_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d___00__closed__4_value)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__5 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__5_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d___00__closed__3_value),((lean_object*)&l_Lean_Json_json_x2d___00__closed__5_value)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__6 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__6_value;
static const lean_string_object l_Lean_Json_json_x2d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Json_json_x2d___00__closed__7 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__7_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_x2d___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__8 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__8_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d___00__closed__8_value)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__9 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__9_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_x2d___00__closed__6_value),((lean_object*)&l_Lean_Json_json_x2d___00__closed__9_value)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__10 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__10_value;
static const lean_ctor_object l_Lean_Json_json_x2d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Json_json_x2d___00__closed__10_value)}};
static const lean_object* l_Lean_Json_json_x2d___00__closed__11 = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Json_json_x2d__ = (const lean_object*)&l_Lean_Json_json_x2d___00__closed__11_value;
static const lean_string_object l_Lean_Json_json_x2d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "json-__1"};
static const lean_object* l_Lean_Json_json_x2d____1___closed__0 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__0_value;
static const lean_ctor_object l_Lean_Json_json_x2d____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_json_x2d____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_json_x2d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_json_x2d____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 117, 171, 240, 190, 70, 117, 11)}};
static const lean_object* l_Lean_Json_json_x2d____1___closed__1 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__1_value;
static const lean_string_object l_Lean_Json_json_x2d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Json_json_x2d____1___closed__2 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__2_value;
static const lean_ctor_object l_Lean_Json_json_x2d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_x2d____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Json_json_x2d____1___closed__3 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__3_value;
static const lean_ctor_object l_Lean_Json_json_x2d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d____1___closed__3_value)}};
static const lean_object* l_Lean_Json_json_x2d____1___closed__4 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__4_value;
static const lean_ctor_object l_Lean_Json_json_x2d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_x2d___00__closed__6_value),((lean_object*)&l_Lean_Json_json_x2d____1___closed__4_value)}};
static const lean_object* l_Lean_Json_json_x2d____1___closed__5 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__5_value;
static const lean_ctor_object l_Lean_Json_json_x2d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_json_x2d____1___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Json_json_x2d____1___closed__5_value)}};
static const lean_object* l_Lean_Json_json_x2d____1___closed__6 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Json_json_x2d____1 = (const lean_object*)&l_Lean_Json_json_x2d____1___closed__6_value;
static const lean_string_object l_Lean_Json_json_x5b___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "json[_]"};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__0 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__0_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 228, 226, 42, 58, 91, 155, 101)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__1 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__1_value;
static const lean_string_object l_Lean_Json_json_x5b___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__2 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__2_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__3 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__3_value;
static const lean_string_object l_Lean_Json_json_x5b___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__4 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__4_value;
static const lean_string_object l_Lean_Json_json_x5b___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__5 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__5_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__5_value)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__6 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__6_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__12_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__4_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__7 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__7_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__3_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__7_value)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__8 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__8_value;
static const lean_string_object l_Lean_Json_json_x5b___x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__9 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__9_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__9_value)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__10 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__10_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__8_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__10_value)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__11 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__11_value;
static const lean_ctor_object l_Lean_Json_json_x5b___x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__11_value)}};
static const lean_object* l_Lean_Json_json_x5b___x5d___closed__12 = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Json_json_x5b___x5d = (const lean_object*)&l_Lean_Json_json_x5b___x5d___closed__12_value;
static const lean_string_object l_Lean_Json_jsonIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "jsonIdent"};
static const lean_object* l_Lean_Json_jsonIdent___closed__0 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__0_value;
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonIdent___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonIdent___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_jsonIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 130, 95, 3, 148, 30, 174, 174)}};
static const lean_object* l_Lean_Json_jsonIdent___closed__1 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__1_value;
static const lean_string_object l_Lean_Json_jsonIdent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Json_jsonIdent___closed__2 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__2_value;
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_jsonIdent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Json_jsonIdent___closed__3 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__3_value;
static const lean_string_object l_Lean_Json_jsonIdent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Json_jsonIdent___closed__4 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__4_value;
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_jsonIdent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Json_jsonIdent___closed__5 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__5_value;
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_jsonIdent___closed__5_value)}};
static const lean_object* l_Lean_Json_jsonIdent___closed__6 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__6_value;
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_jsonIdent___closed__3_value),((lean_object*)&l_Lean_Json_jsonIdent___closed__6_value),((lean_object*)&l_Lean_Json_json___00__closed__4_value)}};
static const lean_object* l_Lean_Json_jsonIdent___closed__7 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__7_value;
static const lean_ctor_object l_Lean_Json_jsonIdent___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Json_jsonIdent___closed__0_value),((lean_object*)&l_Lean_Json_jsonIdent___closed__1_value),((lean_object*)&l_Lean_Json_jsonIdent___closed__7_value)}};
static const lean_object* l_Lean_Json_jsonIdent___closed__8 = (const lean_object*)&l_Lean_Json_jsonIdent___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Json_jsonIdent = (const lean_object*)&l_Lean_Json_jsonIdent___closed__8_value;
static const lean_string_object l_Lean_Json_jsonField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "jsonField"};
static const lean_object* l_Lean_Json_jsonField___closed__0 = (const lean_object*)&l_Lean_Json_jsonField___closed__0_value;
static const lean_ctor_object l_Lean_Json_jsonField___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_jsonField___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonField___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_jsonField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_jsonField___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_jsonField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 231, 71, 34, 65, 247, 44, 17)}};
static const lean_object* l_Lean_Json_jsonField___closed__1 = (const lean_object*)&l_Lean_Json_jsonField___closed__1_value;
static const lean_string_object l_Lean_Json_jsonField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Json_jsonField___closed__2 = (const lean_object*)&l_Lean_Json_jsonField___closed__2_value;
static const lean_ctor_object l_Lean_Json_jsonField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_jsonField___closed__2_value)}};
static const lean_object* l_Lean_Json_jsonField___closed__3 = (const lean_object*)&l_Lean_Json_jsonField___closed__3_value;
static const lean_ctor_object l_Lean_Json_jsonField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_jsonIdent___closed__8_value),((lean_object*)&l_Lean_Json_jsonField___closed__3_value)}};
static const lean_object* l_Lean_Json_jsonField___closed__4 = (const lean_object*)&l_Lean_Json_jsonField___closed__4_value;
static const lean_ctor_object l_Lean_Json_jsonField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_jsonField___closed__4_value),((lean_object*)&l_Lean_Json_json_quot___closed__12_value)}};
static const lean_object* l_Lean_Json_jsonField___closed__5 = (const lean_object*)&l_Lean_Json_jsonField___closed__5_value;
static const lean_ctor_object l_Lean_Json_jsonField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Json_jsonField___closed__0_value),((lean_object*)&l_Lean_Json_jsonField___closed__1_value),((lean_object*)&l_Lean_Json_jsonField___closed__5_value)}};
static const lean_object* l_Lean_Json_jsonField___closed__6 = (const lean_object*)&l_Lean_Json_jsonField___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Json_jsonField = (const lean_object*)&l_Lean_Json_jsonField___closed__6_value;
static const lean_string_object l_Lean_Json_json_x7b___x7d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "json{_}"};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__0 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__0_value;
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 3, 125, 168, 133, 55, 242, 236)}};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__1 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__1_value;
static const lean_string_object l_Lean_Json_json_x7b___x7d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__2 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__2_value;
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__3 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__3_value;
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Json_jsonField___closed__6_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__4_value),((lean_object*)&l_Lean_Json_json_x5b___x5d___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__4 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__4_value;
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__3_value),((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__4_value)}};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__5 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__5_value;
static const lean_string_object l_Lean_Json_json_x7b___x7d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__6 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__6_value;
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__6_value)}};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__7 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__7_value;
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__5_value),((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__7_value)}};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__8 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__8_value;
static const lean_ctor_object l_Lean_Json_json_x7b___x7d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Json_json_x7b___x7d___closed__8_value)}};
static const lean_object* l_Lean_Json_json_x7b___x7d___closed__9 = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Json_json_x7b___x7d = (const lean_object*)&l_Lean_Json_json_x7b___x7d___closed__9_value;
static const lean_string_object l_Lean_Json_termJson_x25___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termJson%_"};
static const lean_object* l_Lean_Json_termJson_x25___00__closed__0 = (const lean_object*)&l_Lean_Json_termJson_x25___00__closed__0_value;
static const lean_ctor_object l_Lean_Json_termJson_x25___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json_termJson_x25___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_termJson_x25___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json_termJson_x25___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_termJson_x25___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Json_termJson_x25___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 92, 195, 143, 253, 86, 166, 134)}};
static const lean_object* l_Lean_Json_termJson_x25___00__closed__1 = (const lean_object*)&l_Lean_Json_termJson_x25___00__closed__1_value;
static const lean_string_object l_Lean_Json_termJson_x25___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "json% "};
static const lean_object* l_Lean_Json_termJson_x25___00__closed__2 = (const lean_object*)&l_Lean_Json_termJson_x25___00__closed__2_value;
static const lean_ctor_object l_Lean_Json_termJson_x25___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_termJson_x25___00__closed__2_value)}};
static const lean_object* l_Lean_Json_termJson_x25___00__closed__3 = (const lean_object*)&l_Lean_Json_termJson_x25___00__closed__3_value;
static const lean_ctor_object l_Lean_Json_termJson_x25___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Json_json_quot___closed__8_value),((lean_object*)&l_Lean_Json_termJson_x25___00__closed__3_value),((lean_object*)&l_Lean_Json_json_quot___closed__12_value)}};
static const lean_object* l_Lean_Json_termJson_x25___00__closed__4 = (const lean_object*)&l_Lean_Json_termJson_x25___00__closed__4_value;
static const lean_ctor_object l_Lean_Json_termJson_x25___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_termJson_x25___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Json_termJson_x25___00__closed__4_value)}};
static const lean_object* l_Lean_Json_termJson_x25___00__closed__5 = (const lean_object*)&l_Lean_Json_termJson_x25___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Json_termJson_x25__ = (const lean_object*)&l_Lean_Json_termJson_x25___00__closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_jsonNull___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value_aux_1),((lean_object*)&l_Lean_Json_json_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value_aux_1),((lean_object*)&l_Lean_Json_json_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__10_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__10_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "json%"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Json_json_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_2),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.toJson"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toJson"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value_aux_0),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(209, 114, 104, 195, 28, 89, 81, 203)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ToJson"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_0),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_1),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(240, 112, 235, 135, 88, 35, 83, 81)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Json.arr"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arr"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_1),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(231, 213, 164, 217, 10, 137, 183, 122)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14_value),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Json.mkObj"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkObj"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_1),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(249, 119, 229, 103, 93, 90, 238, 17)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30_value;
static const lean_array_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Json.num"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_1),((lean_object*)&l_Lean_Json_json_x2d___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(23, 91, 50, 166, 94, 21, 171, 223)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35_value),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_1),((lean_object*)&l_Lean_Json_json_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_2),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term-_"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(77, 127, 37, 42, 155, 196, 209, 131)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Json.str"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_1),((lean_object*)&l_Lean_Json_json___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 69, 190, 82, 239, 242, 166, 242)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47_value),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Json.bool"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bool"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_1),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(184, 44, 107, 247, 27, 17, 33, 5)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55_value),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Bool.false"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value_aux_0),((lean_object*)&l_Lean_Json_jsonFalse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63_value),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Bool.true"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value_aux_0),((lean_object*)&l_Lean_Json_jsonTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70_value),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73_value;
static const lean_string_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Json.null"};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74_value;
static lean_once_cell_t l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_1),((lean_object*)&l_Lean_Json_jsonNull___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 110, 18, 94, 218, 154, 70, 134)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79_value;
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77_value),((lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79_value)}};
static const lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80 = (const lean_object*)&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80_value;
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Category_json(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(uint8_t v___x_275_, size_t v_sz_276_, size_t v_i_277_, lean_object* v_bs_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_lt(v_i_277_, v_sz_276_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v_bs_278_);
return v___x_280_;
}
else
{
lean_object* v_v_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_v_281_ = lean_array_uget(v_bs_278_, v_i_277_);
v___x_282_ = ((lean_object*)(l_Lean_Json_jsonField___closed__1));
lean_inc(v_v_281_);
v___x_283_ = l_Lean_Syntax_isOfKind(v_v_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v_v_281_);
lean_dec_ref(v_bs_278_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v_bs_x27_286_; lean_object* v_ks_287_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v_bs_x27_286_ = lean_array_uset(v_bs_278_, v_i_277_, v___x_285_);
v_ks_287_ = l_Lean_Syntax_getArg(v_v_281_, v___x_285_);
if (v___x_275_ == 0)
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_ks_287_);
v___x_297_ = l_Lean_Syntax_isOfKind(v_ks_287_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec(v_ks_287_);
lean_dec_ref(v_bs_x27_286_);
lean_dec(v_v_281_);
v___x_298_ = lean_box(0);
return v___x_298_;
}
else
{
goto v___jp_288_;
}
}
else
{
goto v___jp_288_;
}
v___jp_288_:
{
lean_object* v___x_289_; lean_object* v_vs_290_; lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_289_ = lean_unsigned_to_nat(2u);
v_vs_290_ = l_Lean_Syntax_getArg(v_v_281_, v___x_289_);
lean_dec(v_v_281_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_ks_287_);
lean_ctor_set(v___x_291_, 1, v_vs_290_);
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_add(v_i_277_, v___x_292_);
v___x_294_ = lean_array_uset(v_bs_x27_286_, v_i_277_, v___x_291_);
v_i_277_ = v___x_293_;
v_bs_278_ = v___x_294_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(lean_object* v___x_299_, lean_object* v_sz_300_, lean_object* v_i_301_, lean_object* v_bs_302_){
_start:
{
uint8_t v___x_32509__boxed_303_; size_t v_sz_boxed_304_; size_t v_i_boxed_305_; lean_object* v_res_306_; 
v___x_32509__boxed_303_ = lean_unbox(v___x_299_);
v_sz_boxed_304_ = lean_unbox_usize(v_sz_300_);
lean_dec(v_sz_300_);
v_i_boxed_305_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_res_306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v___x_32509__boxed_303_, v_sz_boxed_304_, v_i_boxed_305_, v_bs_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(size_t v_sz_307_, size_t v_i_308_, lean_object* v_bs_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_310_ == 0)
{
return v_bs_309_;
}
else
{
lean_object* v_v_311_; lean_object* v_fst_312_; lean_object* v___x_313_; lean_object* v_bs_x27_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v_v_311_ = lean_array_uget_borrowed(v_bs_309_, v_i_308_);
v_fst_312_ = lean_ctor_get(v_v_311_, 0);
lean_inc(v_fst_312_);
v___x_313_ = lean_unsigned_to_nat(0u);
v_bs_x27_314_ = lean_array_uset(v_bs_309_, v_i_308_, v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_308_, v___x_315_);
v___x_317_ = lean_array_uset(v_bs_x27_314_, v_i_308_, v_fst_312_);
v_i_308_ = v___x_316_;
v_bs_309_ = v___x_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(lean_object* v_sz_319_, lean_object* v_i_320_, lean_object* v_bs_321_){
_start:
{
size_t v_sz_boxed_322_; size_t v_i_boxed_323_; lean_object* v_res_324_; 
v_sz_boxed_322_ = lean_unbox_usize(v_sz_319_);
lean_dec(v_sz_319_);
v_i_boxed_323_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v_sz_boxed_322_, v_i_boxed_323_, v_bs_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(size_t v_sz_325_, size_t v_i_326_, lean_object* v_bs_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_328_ == 0)
{
return v_bs_327_;
}
else
{
lean_object* v_v_329_; lean_object* v_snd_330_; lean_object* v___x_331_; lean_object* v_bs_x27_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v_v_329_ = lean_array_uget_borrowed(v_bs_327_, v_i_326_);
v_snd_330_ = lean_ctor_get(v_v_329_, 1);
lean_inc(v_snd_330_);
v___x_331_ = lean_unsigned_to_nat(0u);
v_bs_x27_332_ = lean_array_uset(v_bs_327_, v_i_326_, v___x_331_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_add(v_i_326_, v___x_333_);
v___x_335_ = lean_array_uset(v_bs_x27_332_, v_i_326_, v_snd_330_);
v_i_326_ = v___x_334_;
v_bs_327_ = v___x_335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(lean_object* v_sz_337_, lean_object* v_i_338_, lean_object* v_bs_339_){
_start:
{
size_t v_sz_boxed_340_; size_t v_i_boxed_341_; lean_object* v_res_342_; 
v_sz_boxed_340_ = lean_unbox_usize(v_sz_337_);
lean_dec(v_sz_337_);
v_i_boxed_341_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_boxed_340_, v_i_boxed_341_, v_bs_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(uint8_t v___x_343_, size_t v_sz_344_, size_t v_i_345_, lean_object* v_bs_346_, lean_object* v___y_347_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = lean_usize_dec_lt(v_i_345_, v_sz_344_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_bs_346_);
lean_ctor_set(v___x_349_, 1, v___y_347_);
return v___x_349_;
}
else
{
lean_object* v_v_350_; lean_object* v___x_351_; lean_object* v_bs_x27_352_; lean_object* v_a_354_; lean_object* v_a_355_; lean_object* v___y_361_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_v_350_ = lean_array_uget(v_bs_346_, v_i_345_);
v___x_351_ = lean_unsigned_to_nat(0u);
v_bs_x27_352_ = lean_array_uset(v_bs_346_, v_i_345_, v___x_351_);
v___x_373_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_v_350_);
v___x_374_ = l_Lean_Syntax_isOfKind(v_v_350_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec(v_v_350_);
v___x_375_ = l_Lean_Macro_throwUnsupported___redArg(v___y_347_);
v___y_361_ = v___x_375_;
goto v___jp_360_;
}
else
{
lean_object* v_k_376_; 
v_k_376_ = l_Lean_Syntax_getArg(v_v_350_, v___x_351_);
lean_dec(v_v_350_);
if (v___x_343_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__5));
lean_inc(v_k_376_);
v___x_383_ = l_Lean_Syntax_isOfKind(v_k_376_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v_k_376_);
v___x_385_ = l_Lean_Syntax_isOfKind(v_k_376_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v_k_376_);
v___x_386_ = l_Lean_Macro_throwUnsupported___redArg(v___y_347_);
v___y_361_ = v___x_386_;
goto v___jp_360_;
}
else
{
v_a_354_ = v_k_376_;
v_a_355_ = v___y_347_;
goto v___jp_353_;
}
}
else
{
goto v___jp_377_;
}
}
else
{
goto v___jp_377_;
}
v___jp_377_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = l_Lean_TSyntax_getId(v_k_376_);
lean_dec(v_k_376_);
v___x_379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_378_, v___x_374_);
v___x_380_ = lean_box(2);
v___x_381_ = l_Lean_Syntax_mkStrLit(v___x_379_, v___x_380_);
v_a_354_ = v___x_381_;
v_a_355_ = v___y_347_;
goto v___jp_353_;
}
}
v___jp_353_:
{
size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_345_, v___x_356_);
v___x_358_ = lean_array_uset(v_bs_x27_352_, v_i_345_, v_a_354_);
v_i_345_ = v___x_357_;
v_bs_346_ = v___x_358_;
v___y_347_ = v_a_355_;
goto _start;
}
v___jp_360_:
{
if (lean_obj_tag(v___y_361_) == 0)
{
lean_object* v_a_362_; lean_object* v_a_363_; 
v_a_362_ = lean_ctor_get(v___y_361_, 0);
lean_inc(v_a_362_);
v_a_363_ = lean_ctor_get(v___y_361_, 1);
lean_inc(v_a_363_);
lean_dec_ref_known(v___y_361_, 2);
v_a_354_ = v_a_362_;
v_a_355_ = v_a_363_;
goto v___jp_353_;
}
else
{
lean_object* v_a_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref(v_bs_x27_352_);
v_a_364_ = lean_ctor_get(v___y_361_, 0);
v_a_365_ = lean_ctor_get(v___y_361_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v___y_361_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___y_361_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_inc(v_a_364_);
lean_dec(v___y_361_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_364_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg___boxed(lean_object* v___x_387_, lean_object* v_sz_388_, lean_object* v_i_389_, lean_object* v_bs_390_, lean_object* v___y_391_){
_start:
{
uint8_t v___x_32591__boxed_392_; size_t v_sz_boxed_393_; size_t v_i_boxed_394_; lean_object* v_res_395_; 
v___x_32591__boxed_392_ = lean_unbox(v___x_387_);
v_sz_boxed_393_ = lean_unbox_usize(v_sz_388_);
lean_dec(v_sz_388_);
v_i_boxed_394_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(v___x_32591__boxed_392_, v_sz_boxed_393_, v_i_boxed_394_, v_bs_390_, v___y_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(uint8_t v___x_396_, size_t v_sz_397_, size_t v_i_398_, lean_object* v_bs_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_usize_dec_lt(v_i_398_, v_sz_397_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_bs_399_);
lean_ctor_set(v___x_403_, 1, v___y_401_);
return v___x_403_;
}
else
{
lean_object* v_v_404_; lean_object* v___x_405_; lean_object* v_bs_x27_406_; lean_object* v_a_408_; lean_object* v_a_409_; lean_object* v___y_415_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_v_404_ = lean_array_uget(v_bs_399_, v_i_398_);
v___x_405_ = lean_unsigned_to_nat(0u);
v_bs_x27_406_ = lean_array_uset(v_bs_399_, v_i_398_, v___x_405_);
v___x_427_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_v_404_);
v___x_428_ = l_Lean_Syntax_isOfKind(v_v_404_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec(v_v_404_);
v___x_429_ = l_Lean_Macro_throwUnsupported___redArg(v___y_401_);
v___y_415_ = v___x_429_;
goto v___jp_414_;
}
else
{
lean_object* v_k_430_; 
v_k_430_ = l_Lean_Syntax_getArg(v_v_404_, v___x_405_);
lean_dec(v_v_404_);
if (v___x_396_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__5));
lean_inc(v_k_430_);
v___x_437_ = l_Lean_Syntax_isOfKind(v_k_430_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v_k_430_);
v___x_439_ = l_Lean_Syntax_isOfKind(v_k_430_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_dec(v_k_430_);
v___x_440_ = l_Lean_Macro_throwUnsupported___redArg(v___y_401_);
v___y_415_ = v___x_440_;
goto v___jp_414_;
}
else
{
v_a_408_ = v_k_430_;
v_a_409_ = v___y_401_;
goto v___jp_407_;
}
}
else
{
goto v___jp_431_;
}
}
else
{
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = l_Lean_TSyntax_getId(v_k_430_);
lean_dec(v_k_430_);
v___x_433_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_432_, v___x_428_);
v___x_434_ = lean_box(2);
v___x_435_ = l_Lean_Syntax_mkStrLit(v___x_433_, v___x_434_);
v_a_408_ = v___x_435_;
v_a_409_ = v___y_401_;
goto v___jp_407_;
}
}
v___jp_407_:
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_398_, v___x_410_);
v___x_412_ = lean_array_uset(v_bs_x27_406_, v_i_398_, v_a_408_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(v___x_396_, v_sz_397_, v___x_411_, v___x_412_, v_a_409_);
return v___x_413_;
}
v___jp_414_:
{
if (lean_obj_tag(v___y_415_) == 0)
{
lean_object* v_a_416_; lean_object* v_a_417_; 
v_a_416_ = lean_ctor_get(v___y_415_, 0);
lean_inc(v_a_416_);
v_a_417_ = lean_ctor_get(v___y_415_, 1);
lean_inc(v_a_417_);
lean_dec_ref_known(v___y_415_, 2);
v_a_408_ = v_a_416_;
v_a_409_ = v_a_417_;
goto v___jp_407_;
}
else
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_bs_x27_406_);
v_a_418_ = lean_ctor_get(v___y_415_, 0);
v_a_419_ = lean_ctor_get(v___y_415_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v___y_415_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___y_415_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_inc(v_a_418_);
lean_dec(v___y_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(lean_object* v___x_441_, lean_object* v_sz_442_, lean_object* v_i_443_, lean_object* v_bs_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_32687__boxed_447_; size_t v_sz_boxed_448_; size_t v_i_boxed_449_; lean_object* v_res_450_; 
v___x_32687__boxed_447_ = lean_unbox(v___x_441_);
v_sz_boxed_448_ = lean_unbox_usize(v_sz_442_);
lean_dec(v_sz_442_);
v_i_boxed_449_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_32687__boxed_447_, v_sz_boxed_448_, v_i_boxed_449_, v_bs_444_, v___y_445_, v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_450_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__8));
v___x_471_ = l_String_toRawSubstring_x27(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v___x_483_, size_t v_sz_484_, size_t v_i_485_, lean_object* v_bs_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = lean_usize_dec_lt(v_i_485_, v_sz_484_);
if (v___x_487_ == 0)
{
lean_dec(v___x_483_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
return v_bs_486_;
}
else
{
lean_object* v_v_488_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_526_; 
v_v_488_ = lean_array_uget(v_bs_486_, v_i_485_);
v_fst_489_ = lean_ctor_get(v_v_488_, 0);
v_snd_490_ = lean_ctor_get(v_v_488_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_v_488_);
if (v_isSharedCheck_526_ == 0)
{
v___x_492_ = v_v_488_;
v_isShared_493_ = v_isSharedCheck_526_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snd_490_);
lean_inc(v_fst_489_);
lean_dec(v_v_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_526_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_bs_x27_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_494_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_496_ = lean_unsigned_to_nat(0u);
v_bs_x27_497_ = lean_array_uset(v_bs_486_, v_i_485_, v___x_496_);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2));
v___x_499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
lean_inc(v___x_481_);
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 2);
lean_ctor_set(v___x_492_, 1, v___x_500_);
lean_ctor_set(v___x_492_, 0, v___x_481_);
v___x_502_ = v___x_492_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_525_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_505_ = lean_box(0);
lean_inc(v___x_483_);
lean_inc(v___x_482_);
v___x_506_ = l_Lean_addMacroScope(v___x_482_, v___x_505_, v___x_483_);
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__12));
lean_inc_n(v___x_481_, 10);
v___x_508_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_508_, 0, v___x_481_);
lean_ctor_set(v___x_508_, 1, v___x_504_);
lean_ctor_set(v___x_508_, 2, v___x_506_);
lean_ctor_set(v___x_508_, 3, v___x_507_);
v___x_509_ = l_Lean_Syntax_node1(v___x_481_, v___x_503_, v___x_508_);
v___x_510_ = l_Lean_Syntax_node2(v___x_481_, v___x_499_, v___x_502_, v___x_509_);
v___x_511_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__4));
v___x_512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_481_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13));
v___x_514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_481_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = l_Lean_Syntax_node2(v___x_481_, v___x_494_, v___x_514_, v_snd_490_);
v___x_516_ = l_Lean_Syntax_node1(v___x_481_, v___x_495_, v___x_515_);
v___x_517_ = l_Lean_Syntax_node3(v___x_481_, v___x_495_, v_fst_489_, v___x_512_, v___x_516_);
v___x_518_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_481_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_Syntax_node3(v___x_481_, v___x_498_, v___x_510_, v___x_517_, v___x_519_);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_485_, v___x_521_);
v___x_523_ = lean_array_uset(v_bs_x27_497_, v_i_485_, v___x_520_);
v_i_485_ = v___x_522_;
v_bs_486_ = v___x_523_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___boxed(lean_object* v___x_527_, lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v_sz_530_, lean_object* v_i_531_, lean_object* v_bs_532_){
_start:
{
size_t v_sz_boxed_533_; size_t v_i_boxed_534_; lean_object* v_res_535_; 
v_sz_boxed_533_ = lean_unbox_usize(v_sz_530_);
lean_dec(v_sz_530_);
v_i_boxed_534_ = lean_unbox_usize(v_i_531_);
lean_dec(v_i_531_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v___x_527_, v___x_528_, v___x_529_, v_sz_boxed_533_, v_i_boxed_534_, v_bs_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(size_t v_sz_536_, size_t v_i_537_, lean_object* v_bs_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_537_, v_sz_536_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_bs_538_);
return v___x_540_;
}
else
{
lean_object* v_v_541_; lean_object* v___x_542_; lean_object* v_bs_x27_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v_v_541_ = lean_array_uget(v_bs_538_, v_i_537_);
v___x_542_ = lean_unsigned_to_nat(0u);
v_bs_x27_543_ = lean_array_uset(v_bs_538_, v_i_537_, v___x_542_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_537_, v___x_544_);
v___x_546_ = lean_array_uset(v_bs_x27_543_, v_i_537_, v_v_541_);
v_i_537_ = v___x_545_;
v_bs_538_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0___boxed(lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_boxed_551_, v_i_boxed_552_, v_bs_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(lean_object* v___x_554_, size_t v_sz_555_, size_t v_i_556_, lean_object* v_bs_557_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_lt(v_i_556_, v_sz_555_);
if (v___x_558_ == 0)
{
lean_dec(v___x_554_);
return v_bs_557_;
}
else
{
lean_object* v___x_559_; lean_object* v_v_560_; lean_object* v___x_561_; lean_object* v_bs_x27_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; 
v___x_559_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v_v_560_ = lean_array_uget(v_bs_557_, v_i_556_);
v___x_561_ = lean_unsigned_to_nat(0u);
v_bs_x27_562_ = lean_array_uset(v_bs_557_, v_i_556_, v___x_561_);
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13));
lean_inc_n(v___x_554_, 2);
v___x_564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_554_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_Syntax_node2(v___x_554_, v___x_559_, v___x_564_, v_v_560_);
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_i_556_, v___x_566_);
v___x_568_ = lean_array_uset(v_bs_x27_562_, v_i_556_, v___x_565_);
v_i_556_ = v___x_567_;
v_bs_557_ = v___x_568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1___boxed(lean_object* v___x_570_, lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_bs_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_575_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v___x_570_, v_sz_boxed_574_, v_i_boxed_575_, v_bs_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(uint8_t v___x_577_, uint8_t v___x_578_, lean_object* v_as_579_, size_t v_i_580_, size_t v_stop_581_, lean_object* v_b_582_){
_start:
{
lean_object* v___y_584_; uint8_t v___x_588_; 
v___x_588_ = lean_usize_dec_eq(v_i_580_, v_stop_581_);
if (v___x_588_ == 0)
{
lean_object* v_fst_589_; uint8_t v___x_590_; 
v_fst_589_ = lean_ctor_get(v_b_582_, 0);
v___x_590_ = lean_unbox(v_fst_589_);
if (v___x_590_ == 0)
{
lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_snd_591_ = lean_ctor_get(v_b_582_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_b_582_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_b_582_, 0);
lean_dec(v_unused_600_);
v___x_593_ = v_b_582_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_dec(v_b_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_box(v___x_577_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_snd_591_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
v___y_584_ = v___x_597_;
goto v___jp_583_;
}
}
}
else
{
lean_object* v_snd_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v_snd_601_ = lean_ctor_get(v_b_582_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_b_582_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_b_582_, 0);
lean_dec(v_unused_612_);
v___x_603_ = v_b_582_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snd_601_);
lean_dec(v_b_582_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_605_ = lean_array_uget_borrowed(v_as_579_, v_i_580_);
lean_inc(v___x_605_);
v___x_606_ = lean_array_push(v_snd_601_, v___x_605_);
v___x_607_ = lean_box(v___x_578_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v___x_606_);
lean_ctor_set(v___x_603_, 0, v___x_607_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v___x_606_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
v___y_584_ = v___x_609_;
goto v___jp_583_;
}
}
}
}
else
{
return v_b_582_;
}
v___jp_583_:
{
size_t v___x_585_; size_t v___x_586_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_580_, v___x_585_);
v_i_580_ = v___x_586_;
v_b_582_ = v___y_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7___boxed(lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_as_615_, lean_object* v_i_616_, lean_object* v_stop_617_, lean_object* v_b_618_){
_start:
{
uint8_t v___x_33008__boxed_619_; uint8_t v___x_33009__boxed_620_; size_t v_i_boxed_621_; size_t v_stop_boxed_622_; lean_object* v_res_623_; 
v___x_33008__boxed_619_ = lean_unbox(v___x_613_);
v___x_33009__boxed_620_ = lean_unbox(v___x_614_);
v_i_boxed_621_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_stop_boxed_622_ = lean_unbox_usize(v_stop_617_);
lean_dec(v_stop_617_);
v_res_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_33008__boxed_619_, v___x_33009__boxed_620_, v_as_615_, v_i_boxed_621_, v_stop_boxed_622_, v_b_618_);
lean_dec_ref(v_as_615_);
return v_res_623_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2));
v___x_632_ = l_String_toRawSubstring_x27(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10));
v___x_650_ = l_String_toRawSubstring_x27(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21(void){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Array_mkArray0(lean_box(0));
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__4));
v___x_673_ = l_Lean_mkAtom(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23));
v___x_676_ = l_String_toRawSubstring_x27(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32));
v___x_695_ = l_String_toRawSubstring_x27(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44));
v___x_725_ = l_String_toRawSubstring_x27(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51));
v___x_743_ = l_String_toRawSubstring_x27(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59));
v___x_762_ = l_String_toRawSubstring_x27(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67));
v___x_780_ = l_String_toRawSubstring_x27(v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74));
v___x_797_ = l_String_toRawSubstring_x27(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(lean_object* v_x_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
lean_inc(v_x_813_);
v___x_817_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec(v_x_813_);
v___x_818_ = lean_box(1);
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v_a_815_);
return v___x_819_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_820_ = lean_unsigned_to_nat(1u);
v___x_821_ = l_Lean_Syntax_getArg(v_x_813_, v___x_820_);
lean_dec(v_x_813_);
v___x_822_ = ((lean_object*)(l_Lean_Json_jsonNull___closed__2));
lean_inc(v___x_821_);
v___x_823_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_Json_jsonTrue___closed__1));
lean_inc(v___x_821_);
v___x_825_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_Json_jsonFalse___closed__1));
lean_inc(v___x_821_);
v___x_827_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = ((lean_object*)(l_Lean_Json_json___00__closed__1));
lean_inc(v___x_821_);
v___x_830_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__1));
lean_inc(v___x_821_);
v___x_832_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___y_836_; 
v___x_833_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__1));
lean_inc(v___x_821_);
v___x_834_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___y_888_; 
v___x_885_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__1));
lean_inc(v___x_821_);
v___x_886_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Json_json_x7b___x7d___closed__1));
lean_inc(v___x_821_);
v___x_961_ = l_Lean_Syntax_isOfKind(v___x_821_, v___x_960_);
if (v___x_961_ == 0)
{
uint8_t v___x_962_; 
v___x_962_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v___x_821_);
v___x_963_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_963_;
}
else
{
lean_object* v_quotContext_964_; lean_object* v_currMacroScope_965_; lean_object* v_ref_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_quotContext_964_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_965_ = lean_ctor_get(v_a_814_, 2);
v_ref_966_ = lean_ctor_get(v_a_814_, 5);
v___x_967_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_968_ = l_Lean_SourceInfo_fromRef(v_ref_966_, v___x_961_);
v___x_969_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_970_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_971_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_965_);
lean_inc(v_quotContext_964_);
v___x_972_ = l_Lean_addMacroScope(v_quotContext_964_, v___x_971_, v_currMacroScope_965_);
v___x_973_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_968_, 2);
v___x_974_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_974_, 0, v___x_968_);
lean_ctor_set(v___x_974_, 1, v___x_970_);
lean_ctor_set(v___x_974_, 2, v___x_972_);
lean_ctor_set(v___x_974_, 3, v___x_973_);
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_976_ = l_Lean_Syntax_node1(v___x_968_, v___x_975_, v___x_967_);
v___x_977_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v___x_974_, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_a_815_);
return v___x_978_;
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_979_ = l_Lean_Syntax_getArg(v___x_821_, v___x_820_);
v___x_980_ = l_Lean_Syntax_getArgs(v___x_979_);
lean_dec(v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31));
v___x_982_ = lean_array_get_size(v___x_980_);
v___x_983_ = lean_nat_dec_lt(v___x_828_, v___x_982_);
if (v___x_983_ == 0)
{
lean_dec_ref(v___x_980_);
v___y_888_ = v___x_981_;
goto v___jp_887_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; lean_object* v_snd_989_; 
v___x_984_ = lean_box(v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_981_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_982_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_961_, v___x_886_, v___x_980_, v___x_986_, v___x_987_, v___x_985_);
lean_dec_ref(v___x_980_);
v_snd_989_ = lean_ctor_get(v___x_988_, 1);
lean_inc(v_snd_989_);
lean_dec_ref(v___x_988_);
v___y_888_ = v_snd_989_;
goto v___jp_887_;
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_990_ = l_Lean_Syntax_getArg(v___x_821_, v___x_820_);
v___x_991_ = l_Lean_Syntax_getArgs(v___x_990_);
lean_dec(v___x_990_);
v___x_992_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31));
v___x_993_ = lean_array_get_size(v___x_991_);
v___x_994_ = lean_nat_dec_lt(v___x_828_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_991_);
v___y_836_ = v___x_992_;
goto v___jp_835_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; lean_object* v_snd_1000_; 
v___x_995_ = lean_box(v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_992_);
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_993_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_886_, v___x_834_, v___x_991_, v___x_997_, v___x_998_, v___x_996_);
lean_dec_ref(v___x_991_);
v_snd_1000_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_snd_1000_);
lean_dec_ref(v___x_999_);
v___y_836_ = v_snd_1000_;
goto v___jp_835_;
}
}
v___jp_887_:
{
size_t v_sz_889_; size_t v___x_890_; lean_object* v___x_891_; 
v_sz_889_ = lean_array_size(v___y_888_);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v___x_886_, v_sz_889_, v___x_890_, v___y_888_);
if (lean_obj_tag(v___x_891_) == 0)
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_dec(v___x_821_);
v___x_893_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_893_;
}
else
{
lean_object* v_quotContext_894_; lean_object* v_currMacroScope_895_; lean_object* v_ref_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_quotContext_894_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_895_ = lean_ctor_get(v_a_814_, 2);
v_ref_896_ = lean_ctor_get(v_a_814_, 5);
v___x_897_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_898_ = l_Lean_SourceInfo_fromRef(v_ref_896_, v___x_886_);
v___x_899_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_900_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_901_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_895_);
lean_inc(v_quotContext_894_);
v___x_902_ = l_Lean_addMacroScope(v_quotContext_894_, v___x_901_, v_currMacroScope_895_);
v___x_903_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_898_, 2);
v___x_904_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_904_, 0, v___x_898_);
lean_ctor_set(v___x_904_, 1, v___x_900_);
lean_ctor_set(v___x_904_, 2, v___x_902_);
lean_ctor_set(v___x_904_, 3, v___x_903_);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_906_ = l_Lean_Syntax_node1(v___x_898_, v___x_905_, v___x_897_);
v___x_907_ = l_Lean_Syntax_node2(v___x_898_, v___x_899_, v___x_904_, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v_a_815_);
return v___x_908_;
}
}
else
{
lean_object* v_val_909_; size_t v_sz_910_; lean_object* v_vs_911_; lean_object* v_ks_912_; size_t v_sz_913_; lean_object* v___x_914_; 
lean_dec(v___x_821_);
v_val_909_ = lean_ctor_get(v___x_891_, 0);
lean_inc_n(v_val_909_, 2);
lean_dec_ref_known(v___x_891_, 1);
v_sz_910_ = lean_array_size(v_val_909_);
v_vs_911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_910_, v___x_890_, v_val_909_);
v_ks_912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v_sz_910_, v___x_890_, v_val_909_);
v_sz_913_ = lean_array_size(v_ks_912_);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_886_, v_sz_913_, v___x_890_, v_ks_912_, v_a_814_, v_a_815_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_950_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_a_916_ = lean_ctor_get(v___x_914_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_950_ == 0)
{
v___x_918_ = v___x_914_;
v_isShared_919_ = v_isSharedCheck_950_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_950_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_quotContext_920_; lean_object* v_currMacroScope_921_; lean_object* v_ref_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; size_t v_sz_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v_quotContext_920_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_921_ = lean_ctor_get(v_a_814_, 2);
v_ref_922_ = lean_ctor_get(v_a_814_, 5);
v___x_923_ = l_Lean_SourceInfo_fromRef(v_ref_922_, v___x_886_);
v___x_924_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_925_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24);
v___x_926_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26));
lean_inc_n(v_currMacroScope_921_, 2);
lean_inc_n(v_quotContext_920_, 2);
v___x_927_ = l_Lean_addMacroScope(v_quotContext_920_, v___x_926_, v_currMacroScope_921_);
v___x_928_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28));
lean_inc_n(v___x_923_, 7);
v___x_929_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_929_, 0, v___x_923_);
lean_ctor_set(v___x_929_, 1, v___x_925_);
lean_ctor_set(v___x_929_, 2, v___x_927_);
lean_ctor_set(v___x_929_, 3, v___x_928_);
v___x_930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_931_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30));
v___x_932_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__2));
v___x_933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_923_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
v___x_935_ = l_Array_zip___redArg(v_a_915_, v_vs_911_);
lean_dec_ref(v_vs_911_);
lean_dec(v_a_915_);
v_sz_936_ = lean_array_size(v___x_935_);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v___x_923_, v_quotContext_920_, v_currMacroScope_921_, v_sz_936_, v___x_890_, v___x_935_);
v___x_938_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
v___x_939_ = l_Lean_mkSepArray(v___x_937_, v___x_938_);
lean_dec_ref(v___x_937_);
v___x_940_ = l_Array_append___redArg(v___x_934_, v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_941_, 0, v___x_923_);
lean_ctor_set(v___x_941_, 1, v___x_930_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
v___x_942_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__9));
v___x_943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_923_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_Syntax_node3(v___x_923_, v___x_931_, v___x_933_, v___x_941_, v___x_943_);
v___x_945_ = l_Lean_Syntax_node1(v___x_923_, v___x_930_, v___x_944_);
v___x_946_ = l_Lean_Syntax_node2(v___x_923_, v___x_924_, v___x_929_, v___x_945_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_946_);
v___x_948_ = v___x_918_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_a_916_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v_a_951_; lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v_vs_911_);
v_a_951_ = lean_ctor_get(v___x_914_, 0);
v_a_952_ = lean_ctor_get(v___x_914_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_914_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_inc(v_a_951_);
lean_dec(v___x_914_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_951_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
else
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = l_Lean_Syntax_getArg(v___x_821_, v___x_828_);
lean_inc(v___x_1001_);
v___x_1002_ = l_Lean_Syntax_matchesNull(v___x_1001_, v___x_828_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
v___x_1003_ = l_Lean_Syntax_matchesNull(v___x_1001_, v___x_820_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_dec(v___x_821_);
v___x_1005_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_1005_;
}
else
{
lean_object* v_quotContext_1006_; lean_object* v_currMacroScope_1007_; lean_object* v_ref_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_quotContext_1006_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1007_ = lean_ctor_get(v_a_814_, 2);
v_ref_1008_ = lean_ctor_get(v_a_814_, 5);
v___x_1009_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_1010_ = l_Lean_SourceInfo_fromRef(v_ref_1008_, v___x_1003_);
v___x_1011_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1012_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1013_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1007_);
lean_inc(v_quotContext_1006_);
v___x_1014_ = l_Lean_addMacroScope(v_quotContext_1006_, v___x_1013_, v_currMacroScope_1007_);
v___x_1015_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1010_, 2);
v___x_1016_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1010_);
lean_ctor_set(v___x_1016_, 1, v___x_1012_);
lean_ctor_set(v___x_1016_, 2, v___x_1014_);
lean_ctor_set(v___x_1016_, 3, v___x_1015_);
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1018_ = l_Lean_Syntax_node1(v___x_1010_, v___x_1017_, v___x_1009_);
v___x_1019_ = l_Lean_Syntax_node2(v___x_1010_, v___x_1011_, v___x_1016_, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_a_815_);
return v___x_1020_;
}
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Syntax_getArg(v___x_821_, v___x_820_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_1021_);
v___x_1057_ = l_Lean_Syntax_isOfKind(v___x_1021_, v___x_1056_);
if (v___x_1057_ == 0)
{
uint8_t v___x_1058_; 
lean_dec(v___x_1021_);
v___x_1058_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v___x_821_);
v___x_1059_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_1059_;
}
else
{
lean_object* v_quotContext_1060_; lean_object* v_currMacroScope_1061_; lean_object* v_ref_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_quotContext_1060_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1061_ = lean_ctor_get(v_a_814_, 2);
v_ref_1062_ = lean_ctor_get(v_a_814_, 5);
v___x_1063_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_1064_ = l_Lean_SourceInfo_fromRef(v_ref_1062_, v___x_1002_);
v___x_1065_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1066_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1067_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1061_);
lean_inc(v_quotContext_1060_);
v___x_1068_ = l_Lean_addMacroScope(v_quotContext_1060_, v___x_1067_, v_currMacroScope_1061_);
v___x_1069_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1064_, 2);
v___x_1070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1064_);
lean_ctor_set(v___x_1070_, 1, v___x_1066_);
lean_ctor_set(v___x_1070_, 2, v___x_1068_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
v___x_1071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1072_ = l_Lean_Syntax_node1(v___x_1064_, v___x_1071_, v___x_1063_);
v___x_1073_ = l_Lean_Syntax_node2(v___x_1064_, v___x_1065_, v___x_1070_, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_815_);
return v___x_1074_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1022_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1022_;
}
v___jp_1022_:
{
lean_object* v_quotContext_1023_; lean_object* v_currMacroScope_1024_; lean_object* v_ref_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_quotContext_1023_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1024_ = lean_ctor_get(v_a_814_, 2);
v_ref_1025_ = lean_ctor_get(v_a_814_, 5);
v___x_1026_ = l_Lean_SourceInfo_fromRef(v_ref_1025_, v___x_1002_);
v___x_1027_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1028_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1029_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_1024_, 2);
lean_inc_n(v_quotContext_1023_, 2);
v___x_1030_ = l_Lean_addMacroScope(v_quotContext_1023_, v___x_1029_, v_currMacroScope_1024_);
v___x_1031_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1026_, 10);
v___x_1032_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1026_);
lean_ctor_set(v___x_1032_, 1, v___x_1028_);
lean_ctor_set(v___x_1032_, 2, v___x_1030_);
lean_ctor_set(v___x_1032_, 3, v___x_1031_);
v___x_1033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1034_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
v___x_1037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1026_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_1039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_1040_ = lean_box(0);
v___x_1041_ = l_Lean_addMacroScope(v_quotContext_1023_, v___x_1040_, v_currMacroScope_1024_);
v___x_1042_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_1043_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1026_);
lean_ctor_set(v___x_1043_, 1, v___x_1039_);
lean_ctor_set(v___x_1043_, 2, v___x_1041_);
lean_ctor_set(v___x_1043_, 3, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node1(v___x_1026_, v___x_1038_, v___x_1043_);
v___x_1045_ = l_Lean_Syntax_node2(v___x_1026_, v___x_1035_, v___x_1037_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1047_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1026_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_Syntax_node2(v___x_1026_, v___x_1046_, v___x_1048_, v___x_1021_);
v___x_1050_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1026_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_Syntax_node3(v___x_1026_, v___x_1034_, v___x_1045_, v___x_1049_, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_node1(v___x_1026_, v___x_1033_, v___x_1052_);
v___x_1054_ = l_Lean_Syntax_node2(v___x_1026_, v___x_1027_, v___x_1032_, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v_a_815_);
return v___x_1055_;
}
}
}
else
{
lean_object* v___x_1075_; 
lean_dec(v___x_1001_);
v___x_1075_ = l_Lean_Syntax_getArg(v___x_821_, v___x_820_);
if (v___x_832_ == 0)
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_1075_);
v___x_1092_ = l_Lean_Syntax_isOfKind(v___x_1075_, v___x_1091_);
if (v___x_1092_ == 0)
{
uint8_t v___x_1093_; 
lean_dec(v___x_1075_);
v___x_1093_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec(v___x_821_);
v___x_1094_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_1094_;
}
else
{
lean_object* v_quotContext_1095_; lean_object* v_currMacroScope_1096_; lean_object* v_ref_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_quotContext_1095_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1096_ = lean_ctor_get(v_a_814_, 2);
v_ref_1097_ = lean_ctor_get(v_a_814_, 5);
v___x_1098_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_1099_ = l_Lean_SourceInfo_fromRef(v_ref_1097_, v___x_832_);
v___x_1100_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1101_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1102_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1096_);
lean_inc(v_quotContext_1095_);
v___x_1103_ = l_Lean_addMacroScope(v_quotContext_1095_, v___x_1102_, v_currMacroScope_1096_);
v___x_1104_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1099_, 2);
v___x_1105_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1099_);
lean_ctor_set(v___x_1105_, 1, v___x_1101_);
lean_ctor_set(v___x_1105_, 2, v___x_1103_);
lean_ctor_set(v___x_1105_, 3, v___x_1104_);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1107_ = l_Lean_Syntax_node1(v___x_1099_, v___x_1106_, v___x_1098_);
v___x_1108_ = l_Lean_Syntax_node2(v___x_1099_, v___x_1100_, v___x_1105_, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_a_815_);
return v___x_1109_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1076_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1076_;
}
v___jp_1076_:
{
lean_object* v_quotContext_1077_; lean_object* v_currMacroScope_1078_; lean_object* v_ref_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_quotContext_1077_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1078_ = lean_ctor_get(v_a_814_, 2);
v_ref_1079_ = lean_ctor_get(v_a_814_, 5);
v___x_1080_ = l_Lean_SourceInfo_fromRef(v_ref_1079_, v___x_832_);
v___x_1081_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1082_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1083_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1078_);
lean_inc(v_quotContext_1077_);
v___x_1084_ = l_Lean_addMacroScope(v_quotContext_1077_, v___x_1083_, v_currMacroScope_1078_);
v___x_1085_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1080_, 2);
v___x_1086_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1080_);
lean_ctor_set(v___x_1086_, 1, v___x_1082_);
lean_ctor_set(v___x_1086_, 2, v___x_1084_);
lean_ctor_set(v___x_1086_, 3, v___x_1085_);
v___x_1087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1088_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1087_, v___x_1075_);
v___x_1089_ = l_Lean_Syntax_node2(v___x_1080_, v___x_1081_, v___x_1086_, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_a_815_);
return v___x_1090_;
}
}
}
v___jp_835_:
{
size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; 
v_sz_837_ = lean_array_size(v___y_836_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_837_, v___x_838_, v___y_836_);
if (lean_obj_tag(v___x_839_) == 0)
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v___x_821_);
v___x_841_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_841_;
}
else
{
lean_object* v_quotContext_842_; lean_object* v_currMacroScope_843_; lean_object* v_ref_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_quotContext_842_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_843_ = lean_ctor_get(v_a_814_, 2);
v_ref_844_ = lean_ctor_get(v_a_814_, 5);
v___x_845_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_846_ = l_Lean_SourceInfo_fromRef(v_ref_844_, v___x_834_);
v___x_847_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_848_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_849_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_843_);
lean_inc(v_quotContext_842_);
v___x_850_ = l_Lean_addMacroScope(v_quotContext_842_, v___x_849_, v_currMacroScope_843_);
v___x_851_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_846_, 2);
v___x_852_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_852_, 0, v___x_846_);
lean_ctor_set(v___x_852_, 1, v___x_848_);
lean_ctor_set(v___x_852_, 2, v___x_850_);
lean_ctor_set(v___x_852_, 3, v___x_851_);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_854_ = l_Lean_Syntax_node1(v___x_846_, v___x_853_, v___x_845_);
v___x_855_ = l_Lean_Syntax_node2(v___x_846_, v___x_847_, v___x_852_, v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_a_815_);
return v___x_856_;
}
}
else
{
lean_object* v_val_857_; lean_object* v_quotContext_858_; lean_object* v_currMacroScope_859_; lean_object* v_ref_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; size_t v_sz_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v___x_821_);
v_val_857_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_839_, 1);
v_quotContext_858_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_859_ = lean_ctor_get(v_a_814_, 2);
v_ref_860_ = lean_ctor_get(v_a_814_, 5);
v___x_861_ = l_Lean_SourceInfo_fromRef(v_ref_860_, v___x_834_);
v___x_862_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_863_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11);
v___x_864_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13));
lean_inc(v_currMacroScope_859_);
lean_inc(v_quotContext_858_);
v___x_865_ = l_Lean_addMacroScope(v_quotContext_858_, v___x_864_, v_currMacroScope_859_);
v___x_866_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17));
lean_inc_n(v___x_861_, 7);
v___x_867_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_867_, 0, v___x_861_);
lean_ctor_set(v___x_867_, 1, v___x_863_);
lean_ctor_set(v___x_867_, 2, v___x_865_);
lean_ctor_set(v___x_867_, 3, v___x_866_);
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_869_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19));
v___x_870_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20));
v___x_871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_861_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
v_sz_873_ = lean_array_size(v_val_857_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v___x_861_, v_sz_873_, v___x_838_, v_val_857_);
v___x_875_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
v___x_876_ = l_Lean_mkSepArray(v___x_874_, v___x_875_);
lean_dec_ref(v___x_874_);
v___x_877_ = l_Array_append___redArg(v___x_872_, v___x_876_);
lean_dec_ref(v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_878_, 0, v___x_861_);
lean_ctor_set(v___x_878_, 1, v___x_868_);
lean_ctor_set(v___x_878_, 2, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__9));
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_861_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_Syntax_node3(v___x_861_, v___x_869_, v___x_871_, v___x_878_, v___x_880_);
v___x_882_ = l_Lean_Syntax_node1(v___x_861_, v___x_868_, v___x_881_);
v___x_883_ = l_Lean_Syntax_node2(v___x_861_, v___x_862_, v___x_867_, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_a_815_);
return v___x_884_;
}
}
}
else
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = l_Lean_Syntax_getArg(v___x_821_, v___x_828_);
lean_inc(v___x_1110_);
v___x_1111_ = l_Lean_Syntax_matchesNull(v___x_1110_, v___x_828_);
if (v___x_1111_ == 0)
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_Syntax_matchesNull(v___x_1110_, v___x_820_);
if (v___x_1112_ == 0)
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec(v___x_821_);
v___x_1114_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_1114_;
}
else
{
lean_object* v_quotContext_1115_; lean_object* v_currMacroScope_1116_; lean_object* v_ref_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_quotContext_1115_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1116_ = lean_ctor_get(v_a_814_, 2);
v_ref_1117_ = lean_ctor_get(v_a_814_, 5);
v___x_1118_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_1119_ = l_Lean_SourceInfo_fromRef(v_ref_1117_, v___x_1112_);
v___x_1120_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1121_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1122_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1116_);
lean_inc(v_quotContext_1115_);
v___x_1123_ = l_Lean_addMacroScope(v_quotContext_1115_, v___x_1122_, v_currMacroScope_1116_);
v___x_1124_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1119_, 2);
v___x_1125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1119_);
lean_ctor_set(v___x_1125_, 1, v___x_1121_);
lean_ctor_set(v___x_1125_, 2, v___x_1123_);
lean_ctor_set(v___x_1125_, 3, v___x_1124_);
v___x_1126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1127_ = l_Lean_Syntax_node1(v___x_1119_, v___x_1126_, v___x_1118_);
v___x_1128_ = l_Lean_Syntax_node2(v___x_1119_, v___x_1120_, v___x_1125_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_a_815_);
return v___x_1129_;
}
}
else
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Syntax_getArg(v___x_821_, v___x_820_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1130_);
v___x_1166_ = l_Lean_Syntax_isOfKind(v___x_1130_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; 
lean_dec(v___x_1130_);
v___x_1167_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
lean_dec(v___x_821_);
v___x_1168_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_1168_;
}
else
{
lean_object* v_quotContext_1169_; lean_object* v_currMacroScope_1170_; lean_object* v_ref_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_quotContext_1169_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1170_ = lean_ctor_get(v_a_814_, 2);
v_ref_1171_ = lean_ctor_get(v_a_814_, 5);
v___x_1172_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_1173_ = l_Lean_SourceInfo_fromRef(v_ref_1171_, v___x_1111_);
v___x_1174_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1175_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1176_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1170_);
lean_inc(v_quotContext_1169_);
v___x_1177_ = l_Lean_addMacroScope(v_quotContext_1169_, v___x_1176_, v_currMacroScope_1170_);
v___x_1178_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1173_, 2);
v___x_1179_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1173_);
lean_ctor_set(v___x_1179_, 1, v___x_1175_);
lean_ctor_set(v___x_1179_, 2, v___x_1177_);
lean_ctor_set(v___x_1179_, 3, v___x_1178_);
v___x_1180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1181_ = l_Lean_Syntax_node1(v___x_1173_, v___x_1180_, v___x_1172_);
v___x_1182_ = l_Lean_Syntax_node2(v___x_1173_, v___x_1174_, v___x_1179_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v_a_815_);
return v___x_1183_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1131_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1131_;
}
v___jp_1131_:
{
lean_object* v_quotContext_1132_; lean_object* v_currMacroScope_1133_; lean_object* v_ref_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_quotContext_1132_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1133_ = lean_ctor_get(v_a_814_, 2);
v_ref_1134_ = lean_ctor_get(v_a_814_, 5);
v___x_1135_ = l_Lean_SourceInfo_fromRef(v_ref_1134_, v___x_1111_);
v___x_1136_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1137_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1138_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_1133_, 2);
lean_inc_n(v_quotContext_1132_, 2);
v___x_1139_ = l_Lean_addMacroScope(v_quotContext_1132_, v___x_1138_, v_currMacroScope_1133_);
v___x_1140_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1135_, 10);
v___x_1141_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1135_);
lean_ctor_set(v___x_1141_, 1, v___x_1137_);
lean_ctor_set(v___x_1141_, 2, v___x_1139_);
lean_ctor_set(v___x_1141_, 3, v___x_1140_);
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1143_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
v___x_1146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1135_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_1148_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Lean_addMacroScope(v_quotContext_1132_, v___x_1149_, v_currMacroScope_1133_);
v___x_1151_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_1152_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1135_);
lean_ctor_set(v___x_1152_, 1, v___x_1148_);
lean_ctor_set(v___x_1152_, 2, v___x_1150_);
lean_ctor_set(v___x_1152_, 3, v___x_1151_);
v___x_1153_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1147_, v___x_1152_);
v___x_1154_ = l_Lean_Syntax_node2(v___x_1135_, v___x_1144_, v___x_1146_, v___x_1153_);
v___x_1155_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1156_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1135_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_Syntax_node2(v___x_1135_, v___x_1155_, v___x_1157_, v___x_1130_);
v___x_1159_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1135_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_Syntax_node3(v___x_1135_, v___x_1143_, v___x_1154_, v___x_1158_, v___x_1160_);
v___x_1162_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1142_, v___x_1161_);
v___x_1163_ = l_Lean_Syntax_node2(v___x_1135_, v___x_1136_, v___x_1141_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v_a_815_);
return v___x_1164_;
}
}
}
else
{
lean_object* v___x_1184_; 
lean_dec(v___x_1110_);
v___x_1184_ = l_Lean_Syntax_getArg(v___x_821_, v___x_820_);
if (v___x_830_ == 0)
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1184_);
v___x_1201_ = l_Lean_Syntax_isOfKind(v___x_1184_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
lean_dec(v___x_1184_);
v___x_1202_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
lean_dec(v___x_821_);
v___x_1203_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_1203_;
}
else
{
lean_object* v_quotContext_1204_; lean_object* v_currMacroScope_1205_; lean_object* v_ref_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_quotContext_1204_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1205_ = lean_ctor_get(v_a_814_, 2);
v_ref_1206_ = lean_ctor_get(v_a_814_, 5);
v___x_1207_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_1208_ = l_Lean_SourceInfo_fromRef(v_ref_1206_, v___x_830_);
v___x_1209_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1210_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1211_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1205_);
lean_inc(v_quotContext_1204_);
v___x_1212_ = l_Lean_addMacroScope(v_quotContext_1204_, v___x_1211_, v_currMacroScope_1205_);
v___x_1213_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1208_, 2);
v___x_1214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1208_);
lean_ctor_set(v___x_1214_, 1, v___x_1210_);
lean_ctor_set(v___x_1214_, 2, v___x_1212_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
v___x_1215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1216_ = l_Lean_Syntax_node1(v___x_1208_, v___x_1215_, v___x_1207_);
v___x_1217_ = l_Lean_Syntax_node2(v___x_1208_, v___x_1209_, v___x_1214_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_a_815_);
return v___x_1218_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1185_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1185_;
}
v___jp_1185_:
{
lean_object* v_quotContext_1186_; lean_object* v_currMacroScope_1187_; lean_object* v_ref_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_quotContext_1186_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1187_ = lean_ctor_get(v_a_814_, 2);
v_ref_1188_ = lean_ctor_get(v_a_814_, 5);
v___x_1189_ = l_Lean_SourceInfo_fromRef(v_ref_1188_, v___x_830_);
v___x_1190_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1191_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1192_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1187_);
lean_inc(v_quotContext_1186_);
v___x_1193_ = l_Lean_addMacroScope(v_quotContext_1186_, v___x_1192_, v_currMacroScope_1187_);
v___x_1194_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1189_, 2);
v___x_1195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v___x_1191_);
lean_ctor_set(v___x_1195_, 2, v___x_1193_);
lean_ctor_set(v___x_1195_, 3, v___x_1194_);
v___x_1196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1197_ = l_Lean_Syntax_node1(v___x_1189_, v___x_1196_, v___x_1184_);
v___x_1198_ = l_Lean_Syntax_node2(v___x_1189_, v___x_1190_, v___x_1195_, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_a_815_);
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Syntax_getArg(v___x_821_, v___x_828_);
if (v___x_827_ == 0)
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v___x_1219_);
v___x_1236_ = l_Lean_Syntax_isOfKind(v___x_1219_, v___x_1235_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; 
lean_dec(v___x_1219_);
v___x_1237_ = l_Lean_Syntax_isAntiquot(v___x_821_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec(v___x_821_);
v___x_1238_ = l_Lean_Macro_throwUnsupported___redArg(v_a_815_);
return v___x_1238_;
}
else
{
lean_object* v_quotContext_1239_; lean_object* v_currMacroScope_1240_; lean_object* v_ref_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_quotContext_1239_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1240_ = lean_ctor_get(v_a_814_, 2);
v_ref_1241_ = lean_ctor_get(v_a_814_, 5);
v___x_1242_ = l_Lean_Syntax_getAntiquotTerm(v___x_821_);
lean_dec(v___x_821_);
v___x_1243_ = l_Lean_SourceInfo_fromRef(v_ref_1241_, v___x_827_);
v___x_1244_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1245_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1246_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1240_);
lean_inc(v_quotContext_1239_);
v___x_1247_ = l_Lean_addMacroScope(v_quotContext_1239_, v___x_1246_, v_currMacroScope_1240_);
v___x_1248_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1243_, 2);
v___x_1249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1243_);
lean_ctor_set(v___x_1249_, 1, v___x_1245_);
lean_ctor_set(v___x_1249_, 2, v___x_1247_);
lean_ctor_set(v___x_1249_, 3, v___x_1248_);
v___x_1250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1251_ = l_Lean_Syntax_node1(v___x_1243_, v___x_1250_, v___x_1242_);
v___x_1252_ = l_Lean_Syntax_node2(v___x_1243_, v___x_1244_, v___x_1249_, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v_a_815_);
return v___x_1253_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1220_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v_quotContext_1221_; lean_object* v_currMacroScope_1222_; lean_object* v_ref_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_quotContext_1221_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1222_ = lean_ctor_get(v_a_814_, 2);
v_ref_1223_ = lean_ctor_get(v_a_814_, 5);
v___x_1224_ = l_Lean_SourceInfo_fromRef(v_ref_1223_, v___x_827_);
v___x_1225_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1226_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45);
v___x_1227_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46));
lean_inc(v_currMacroScope_1222_);
lean_inc(v_quotContext_1221_);
v___x_1228_ = l_Lean_addMacroScope(v_quotContext_1221_, v___x_1227_, v_currMacroScope_1222_);
v___x_1229_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50));
lean_inc_n(v___x_1224_, 2);
v___x_1230_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1224_);
lean_ctor_set(v___x_1230_, 1, v___x_1226_);
lean_ctor_set(v___x_1230_, 2, v___x_1228_);
lean_ctor_set(v___x_1230_, 3, v___x_1229_);
v___x_1231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1232_ = l_Lean_Syntax_node1(v___x_1224_, v___x_1231_, v___x_1219_);
v___x_1233_ = l_Lean_Syntax_node2(v___x_1224_, v___x_1225_, v___x_1230_, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_a_815_);
return v___x_1234_;
}
}
}
else
{
lean_object* v_quotContext_1254_; lean_object* v_currMacroScope_1255_; lean_object* v_ref_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec(v___x_821_);
v_quotContext_1254_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1255_ = lean_ctor_get(v_a_814_, 2);
v_ref_1256_ = lean_ctor_get(v_a_814_, 5);
v___x_1257_ = l_Lean_SourceInfo_fromRef(v_ref_1256_, v___x_825_);
v___x_1258_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1259_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1260_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1255_, 2);
lean_inc_n(v_quotContext_1254_, 2);
v___x_1261_ = l_Lean_addMacroScope(v_quotContext_1254_, v___x_1260_, v_currMacroScope_1255_);
v___x_1262_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1257_, 3);
v___x_1263_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1257_);
lean_ctor_set(v___x_1263_, 1, v___x_1259_);
lean_ctor_set(v___x_1263_, 2, v___x_1261_);
lean_ctor_set(v___x_1263_, 3, v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1265_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60);
v___x_1266_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62));
v___x_1267_ = l_Lean_addMacroScope(v_quotContext_1254_, v___x_1266_, v_currMacroScope_1255_);
v___x_1268_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66));
v___x_1269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1257_);
lean_ctor_set(v___x_1269_, 1, v___x_1265_);
lean_ctor_set(v___x_1269_, 2, v___x_1267_);
lean_ctor_set(v___x_1269_, 3, v___x_1268_);
v___x_1270_ = l_Lean_Syntax_node1(v___x_1257_, v___x_1264_, v___x_1269_);
v___x_1271_ = l_Lean_Syntax_node2(v___x_1257_, v___x_1258_, v___x_1263_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_815_);
return v___x_1272_;
}
}
else
{
lean_object* v_quotContext_1273_; lean_object* v_currMacroScope_1274_; lean_object* v_ref_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v___x_821_);
v_quotContext_1273_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1274_ = lean_ctor_get(v_a_814_, 2);
v_ref_1275_ = lean_ctor_get(v_a_814_, 5);
v___x_1276_ = l_Lean_SourceInfo_fromRef(v_ref_1275_, v___x_823_);
v___x_1277_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1278_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1279_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1274_, 2);
lean_inc_n(v_quotContext_1273_, 2);
v___x_1280_ = l_Lean_addMacroScope(v_quotContext_1273_, v___x_1279_, v_currMacroScope_1274_);
v___x_1281_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1276_, 3);
v___x_1282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1276_);
lean_ctor_set(v___x_1282_, 1, v___x_1278_);
lean_ctor_set(v___x_1282_, 2, v___x_1280_);
lean_ctor_set(v___x_1282_, 3, v___x_1281_);
v___x_1283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1284_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68);
v___x_1285_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69));
v___x_1286_ = l_Lean_addMacroScope(v_quotContext_1273_, v___x_1285_, v_currMacroScope_1274_);
v___x_1287_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73));
v___x_1288_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1276_);
lean_ctor_set(v___x_1288_, 1, v___x_1284_);
lean_ctor_set(v___x_1288_, 2, v___x_1286_);
lean_ctor_set(v___x_1288_, 3, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_node1(v___x_1276_, v___x_1283_, v___x_1288_);
v___x_1290_ = l_Lean_Syntax_node2(v___x_1276_, v___x_1277_, v___x_1282_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_a_815_);
return v___x_1291_;
}
}
else
{
lean_object* v_quotContext_1292_; lean_object* v_currMacroScope_1293_; lean_object* v_ref_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec(v___x_821_);
v_quotContext_1292_ = lean_ctor_get(v_a_814_, 1);
v_currMacroScope_1293_ = lean_ctor_get(v_a_814_, 2);
v_ref_1294_ = lean_ctor_get(v_a_814_, 5);
v___x_1295_ = 0;
v___x_1296_ = l_Lean_SourceInfo_fromRef(v_ref_1294_, v___x_1295_);
v___x_1297_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75);
v___x_1298_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76));
lean_inc(v_currMacroScope_1293_);
lean_inc(v_quotContext_1292_);
v___x_1299_ = l_Lean_addMacroScope(v_quotContext_1292_, v___x_1298_, v_currMacroScope_1293_);
v___x_1300_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80));
v___x_1301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1296_);
lean_ctor_set(v___x_1301_, 1, v___x_1297_);
lean_ctor_set(v___x_1301_, 2, v___x_1299_);
lean_ctor_set(v___x_1301_, 3, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_a_815_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___boxed(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(v_x_1303_, v_a_1304_, v_a_1305_);
lean_dec_ref(v_a_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5(uint8_t v___x_1307_, size_t v_sz_1308_, size_t v_i_1309_, lean_object* v_bs_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(v___x_1307_, v_sz_1308_, v_i_1309_, v_bs_1310_, v___y_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___boxed(lean_object* v___x_1314_, lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_bs_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v___x_35052__boxed_1320_; size_t v_sz_boxed_1321_; size_t v_i_boxed_1322_; lean_object* v_res_1323_; 
v___x_35052__boxed_1320_ = lean_unbox(v___x_1314_);
v_sz_boxed_1321_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1322_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5(v___x_35052__boxed_1320_, v_sz_boxed_1321_, v_i_boxed_1322_, v_bs_1317_, v___y_1318_, v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Elab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Json_FromToJson(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_Elab(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Category_json = _init_l_Lean_Parser_Category_json();
lean_mark_persistent(l_Lean_Parser_Category_json);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_FromToJson(uint8_t builtin);
lean_object* initialize_Lean_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Elab(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_FromToJson(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_Elab(builtin);
}
#ifdef __cplusplus
}
#endif
