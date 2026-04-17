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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_jsonNull___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_1),((lean_object*)&l_Lean_Json_json_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_0),((lean_object*)&l_Lean_Json_json_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_1),((lean_object*)&l_Lean_Json_json_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Json_json_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value_aux_0),((lean_object*)&l_Lean_Json_jsonNull___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "json%"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Category_json(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(size_t v_sz_275_, size_t v_i_276_, lean_object* v_bs_277_, lean_object* v___y_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_lt(v_i_276_, v_sz_275_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_bs_277_);
lean_ctor_set(v___x_280_, 1, v___y_278_);
return v___x_280_;
}
else
{
lean_object* v_v_281_; lean_object* v___x_282_; lean_object* v_bs_x27_283_; lean_object* v_a_285_; lean_object* v_a_286_; lean_object* v___y_292_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_v_281_ = lean_array_uget(v_bs_277_, v_i_276_);
v___x_282_ = lean_unsigned_to_nat(0u);
v_bs_x27_283_ = lean_array_uset(v_bs_277_, v_i_276_, v___x_282_);
v___x_304_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_v_281_);
v___x_305_ = l_Lean_Syntax_isOfKind(v_v_281_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v_v_281_);
v___x_306_ = l_Lean_Macro_throwUnsupported___redArg(v___y_278_);
v___y_292_ = v___x_306_;
goto v___jp_291_;
}
else
{
lean_object* v_k_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_k_307_ = l_Lean_Syntax_getArg(v_v_281_, v___x_282_);
lean_dec(v_v_281_);
v___x_308_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__5));
lean_inc(v_k_307_);
v___x_309_ = l_Lean_Syntax_isOfKind(v_k_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v_k_307_);
v___x_311_ = l_Lean_Syntax_isOfKind(v_k_307_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec(v_k_307_);
v___x_312_ = l_Lean_Macro_throwUnsupported___redArg(v___y_278_);
v___y_292_ = v___x_312_;
goto v___jp_291_;
}
else
{
v_a_285_ = v_k_307_;
v_a_286_ = v___y_278_;
goto v___jp_284_;
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = l_Lean_TSyntax_getId(v_k_307_);
lean_dec(v_k_307_);
v___x_314_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_313_, v___x_309_);
v___x_315_ = lean_box(2);
v___x_316_ = l_Lean_Syntax_mkStrLit(v___x_314_, v___x_315_);
v_a_285_ = v___x_316_;
v_a_286_ = v___y_278_;
goto v___jp_284_;
}
}
v___jp_284_:
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_i_276_, v___x_287_);
v___x_289_ = lean_array_uset(v_bs_x27_283_, v_i_276_, v_a_285_);
v_i_276_ = v___x_288_;
v_bs_277_ = v___x_289_;
v___y_278_ = v_a_286_;
goto _start;
}
v___jp_291_:
{
if (lean_obj_tag(v___y_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_a_294_; 
v_a_293_ = lean_ctor_get(v___y_292_, 0);
lean_inc(v_a_293_);
v_a_294_ = lean_ctor_get(v___y_292_, 1);
lean_inc(v_a_294_);
lean_dec_ref(v___y_292_);
v_a_285_ = v_a_293_;
v_a_286_ = v_a_294_;
goto v___jp_284_;
}
else
{
lean_object* v_a_295_; lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v_bs_x27_283_);
v_a_295_ = lean_ctor_get(v___y_292_, 0);
v_a_296_ = lean_ctor_get(v___y_292_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v___y_292_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___y_292_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_inc(v_a_295_);
lean_dec(v___y_292_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_295_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg___boxed(lean_object* v_sz_317_, lean_object* v_i_318_, lean_object* v_bs_319_, lean_object* v___y_320_){
_start:
{
size_t v_sz_boxed_321_; size_t v_i_boxed_322_; lean_object* v_res_323_; 
v_sz_boxed_321_ = lean_unbox_usize(v_sz_317_);
lean_dec(v_sz_317_);
v_i_boxed_322_ = lean_unbox_usize(v_i_318_);
lean_dec(v_i_318_);
v_res_323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(v_sz_boxed_321_, v_i_boxed_322_, v_bs_319_, v___y_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(size_t v_sz_324_, size_t v_i_325_, lean_object* v_bs_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_327_ == 0)
{
return v_bs_326_;
}
else
{
lean_object* v_v_328_; lean_object* v_fst_329_; lean_object* v___x_330_; lean_object* v_bs_x27_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_v_328_ = lean_array_uget_borrowed(v_bs_326_, v_i_325_);
v_fst_329_ = lean_ctor_get(v_v_328_, 0);
lean_inc(v_fst_329_);
v___x_330_ = lean_unsigned_to_nat(0u);
v_bs_x27_331_ = lean_array_uset(v_bs_326_, v_i_325_, v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_325_, v___x_332_);
v___x_334_ = lean_array_uset(v_bs_x27_331_, v_i_325_, v_fst_329_);
v_i_325_ = v___x_333_;
v_bs_326_ = v___x_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(lean_object* v_sz_336_, lean_object* v_i_337_, lean_object* v_bs_338_){
_start:
{
size_t v_sz_boxed_339_; size_t v_i_boxed_340_; lean_object* v_res_341_; 
v_sz_boxed_339_ = lean_unbox_usize(v_sz_336_);
lean_dec(v_sz_336_);
v_i_boxed_340_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v_sz_boxed_339_, v_i_boxed_340_, v_bs_338_);
return v_res_341_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8));
v___x_362_ = l_String_toRawSubstring_x27(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(lean_object* v___x_372_, lean_object* v___x_373_, lean_object* v___x_374_, size_t v_sz_375_, size_t v_i_376_, lean_object* v_bs_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_lt(v_i_376_, v_sz_375_);
if (v___x_378_ == 0)
{
lean_dec(v___x_374_);
lean_dec(v___x_373_);
lean_dec(v___x_372_);
return v_bs_377_;
}
else
{
lean_object* v_v_379_; lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_417_; 
v_v_379_ = lean_array_uget(v_bs_377_, v_i_376_);
v_fst_380_ = lean_ctor_get(v_v_379_, 0);
v_snd_381_ = lean_ctor_get(v_v_379_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_v_379_);
if (v_isSharedCheck_417_ == 0)
{
v___x_383_ = v_v_379_;
v_isShared_384_ = v_isSharedCheck_417_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_inc(v_fst_380_);
lean_dec(v_v_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_417_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_bs_x27_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_385_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_387_ = lean_unsigned_to_nat(0u);
v_bs_x27_388_ = lean_array_uset(v_bs_377_, v_i_376_, v___x_387_);
v___x_389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2));
v___x_390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4));
v___x_391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5));
lean_inc(v___x_372_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 2);
lean_ctor_set(v___x_383_, 1, v___x_391_);
lean_ctor_set(v___x_383_, 0, v___x_372_);
v___x_393_ = v___x_383_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_391_);
v___x_393_ = v_reuseFailAlloc_416_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; size_t v___x_412_; size_t v___x_413_; lean_object* v___x_414_; 
v___x_394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7));
v___x_395_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9);
v___x_396_ = lean_box(0);
lean_inc(v___x_374_);
lean_inc(v___x_373_);
v___x_397_ = l_Lean_addMacroScope(v___x_373_, v___x_396_, v___x_374_);
v___x_398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12));
lean_inc_n(v___x_372_, 10);
v___x_399_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_399_, 0, v___x_372_);
lean_ctor_set(v___x_399_, 1, v___x_395_);
lean_ctor_set(v___x_399_, 2, v___x_397_);
lean_ctor_set(v___x_399_, 3, v___x_398_);
v___x_400_ = l_Lean_Syntax_node1(v___x_372_, v___x_394_, v___x_399_);
v___x_401_ = l_Lean_Syntax_node2(v___x_372_, v___x_390_, v___x_393_, v___x_400_);
v___x_402_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__4));
v___x_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_372_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13));
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_372_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_Syntax_node2(v___x_372_, v___x_385_, v___x_405_, v_snd_381_);
v___x_407_ = l_Lean_Syntax_node1(v___x_372_, v___x_386_, v___x_406_);
v___x_408_ = l_Lean_Syntax_node3(v___x_372_, v___x_386_, v_fst_380_, v___x_403_, v___x_407_);
v___x_409_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_372_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l_Lean_Syntax_node3(v___x_372_, v___x_389_, v___x_401_, v___x_408_, v___x_410_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_add(v_i_376_, v___x_412_);
v___x_414_ = lean_array_uset(v_bs_x27_388_, v_i_376_, v___x_411_);
v_i_376_ = v___x_413_;
v_bs_377_ = v___x_414_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_sz_421_, lean_object* v_i_422_, lean_object* v_bs_423_){
_start:
{
size_t v_sz_boxed_424_; size_t v_i_boxed_425_; lean_object* v_res_426_; 
v_sz_boxed_424_ = lean_unbox_usize(v_sz_421_);
lean_dec(v_sz_421_);
v_i_boxed_425_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v___x_418_, v___x_419_, v___x_420_, v_sz_boxed_424_, v_i_boxed_425_, v_bs_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(size_t v_sz_427_, size_t v_i_428_, lean_object* v_bs_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_bs_429_);
return v___x_431_;
}
else
{
lean_object* v_v_432_; lean_object* v___x_433_; lean_object* v_bs_x27_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v_v_432_ = lean_array_uget(v_bs_429_, v_i_428_);
v___x_433_ = lean_unsigned_to_nat(0u);
v_bs_x27_434_ = lean_array_uset(v_bs_429_, v_i_428_, v___x_433_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_i_428_, v___x_435_);
v___x_437_ = lean_array_uset(v_bs_x27_434_, v_i_428_, v_v_432_);
v_i_428_ = v___x_436_;
v_bs_429_ = v___x_437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___boxed(lean_object* v_sz_439_, lean_object* v_i_440_, lean_object* v_bs_441_){
_start:
{
size_t v_sz_boxed_442_; size_t v_i_boxed_443_; lean_object* v_res_444_; 
v_sz_boxed_442_ = lean_unbox_usize(v_sz_439_);
lean_dec(v_sz_439_);
v_i_boxed_443_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v_sz_boxed_442_, v_i_boxed_443_, v_bs_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(uint8_t v___x_445_, uint8_t v___x_446_, lean_object* v_as_447_, size_t v_i_448_, size_t v_stop_449_, lean_object* v_b_450_){
_start:
{
lean_object* v___y_452_; uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_eq(v_i_448_, v_stop_449_);
if (v___x_456_ == 0)
{
lean_object* v_fst_457_; uint8_t v___x_458_; 
v_fst_457_ = lean_ctor_get(v_b_450_, 0);
v___x_458_ = lean_unbox(v_fst_457_);
if (v___x_458_ == 0)
{
lean_object* v_snd_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_snd_459_ = lean_ctor_get(v_b_450_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_b_450_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v_b_450_, 0);
lean_dec(v_unused_468_);
v___x_461_ = v_b_450_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_snd_459_);
lean_dec(v_b_450_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_box(v___x_445_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_snd_459_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
v___y_452_ = v___x_465_;
goto v___jp_451_;
}
}
}
else
{
lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_479_; 
v_snd_469_ = lean_ctor_get(v_b_450_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_b_450_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v_b_450_, 0);
lean_dec(v_unused_480_);
v___x_471_ = v_b_450_;
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_dec(v_b_450_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_473_ = lean_array_uget_borrowed(v_as_447_, v_i_448_);
lean_inc(v___x_473_);
v___x_474_ = lean_array_push(v_snd_469_, v___x_473_);
v___x_475_ = lean_box(v___x_446_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_474_);
lean_ctor_set(v___x_471_, 0, v___x_475_);
v___x_477_ = v___x_471_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_474_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v___y_452_ = v___x_477_;
goto v___jp_451_;
}
}
}
}
else
{
return v_b_450_;
}
v___jp_451_:
{
size_t v___x_453_; size_t v___x_454_; 
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_add(v_i_448_, v___x_453_);
v_i_448_ = v___x_454_;
v_b_450_ = v___y_452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_stop_485_, lean_object* v_b_486_){
_start:
{
uint8_t v___x_67873__boxed_487_; uint8_t v___x_67874__boxed_488_; size_t v_i_boxed_489_; size_t v_stop_boxed_490_; lean_object* v_res_491_; 
v___x_67873__boxed_487_ = lean_unbox(v___x_481_);
v___x_67874__boxed_488_ = lean_unbox(v___x_482_);
v_i_boxed_489_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_stop_boxed_490_ = lean_unbox_usize(v_stop_485_);
lean_dec(v_stop_485_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_67873__boxed_487_, v___x_67874__boxed_488_, v_as_483_, v_i_boxed_489_, v_stop_boxed_490_, v_b_486_);
lean_dec_ref(v_as_483_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(size_t v_sz_492_, size_t v_i_493_, lean_object* v_bs_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_bs_494_);
return v___x_496_;
}
else
{
lean_object* v_v_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_v_497_ = lean_array_uget(v_bs_494_, v_i_493_);
v___x_498_ = ((lean_object*)(l_Lean_Json_jsonField___closed__1));
lean_inc(v_v_497_);
v___x_499_ = l_Lean_Syntax_isOfKind(v_v_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec(v_v_497_);
lean_dec_ref(v_bs_494_);
v___x_500_ = lean_box(0);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v_ks_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v_ks_502_ = l_Lean_Syntax_getArg(v_v_497_, v___x_501_);
v___x_503_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_ks_502_);
v___x_504_ = l_Lean_Syntax_isOfKind(v_ks_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v_ks_502_);
lean_dec(v_v_497_);
lean_dec_ref(v_bs_494_);
v___x_505_ = lean_box(0);
return v___x_505_;
}
else
{
lean_object* v_bs_x27_506_; lean_object* v___x_507_; lean_object* v_vs_508_; lean_object* v___x_509_; size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; 
v_bs_x27_506_ = lean_array_uset(v_bs_494_, v_i_493_, v___x_501_);
v___x_507_ = lean_unsigned_to_nat(2u);
v_vs_508_ = l_Lean_Syntax_getArg(v_v_497_, v___x_507_);
lean_dec(v_v_497_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_ks_502_);
lean_ctor_set(v___x_509_, 1, v_vs_508_);
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_add(v_i_493_, v___x_510_);
v___x_512_ = lean_array_uset(v_bs_x27_506_, v_i_493_, v___x_509_);
v_i_493_ = v___x_511_;
v_bs_494_ = v___x_512_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0___boxed(lean_object* v_sz_514_, lean_object* v_i_515_, lean_object* v_bs_516_){
_start:
{
size_t v_sz_boxed_517_; size_t v_i_boxed_518_; lean_object* v_res_519_; 
v_sz_boxed_517_ = lean_unbox_usize(v_sz_514_);
lean_dec(v_sz_514_);
v_i_boxed_518_ = lean_unbox_usize(v_i_515_);
lean_dec(v_i_515_);
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_boxed_517_, v_i_boxed_518_, v_bs_516_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(lean_object* v___x_520_, size_t v_sz_521_, size_t v_i_522_, lean_object* v_bs_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_lt(v_i_522_, v_sz_521_);
if (v___x_524_ == 0)
{
lean_dec(v___x_520_);
return v_bs_523_;
}
else
{
lean_object* v___x_525_; lean_object* v_v_526_; lean_object* v___x_527_; lean_object* v_bs_x27_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v___x_525_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v_v_526_ = lean_array_uget(v_bs_523_, v_i_522_);
v___x_527_ = lean_unsigned_to_nat(0u);
v_bs_x27_528_ = lean_array_uset(v_bs_523_, v_i_522_, v___x_527_);
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13));
lean_inc_n(v___x_520_, 2);
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_520_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_Syntax_node2(v___x_520_, v___x_525_, v___x_530_, v_v_526_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_522_, v___x_532_);
v___x_534_ = lean_array_uset(v_bs_x27_528_, v_i_522_, v___x_531_);
v_i_522_ = v___x_533_;
v_bs_523_ = v___x_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7___boxed(lean_object* v___x_536_, lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_bs_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_541_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_536_, v_sz_boxed_540_, v_i_boxed_541_, v_bs_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(size_t v_sz_543_, size_t v_i_544_, lean_object* v_bs_545_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = lean_usize_dec_lt(v_i_544_, v_sz_543_);
if (v___x_546_ == 0)
{
return v_bs_545_;
}
else
{
lean_object* v_v_547_; lean_object* v_snd_548_; lean_object* v___x_549_; lean_object* v_bs_x27_550_; size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v_v_547_ = lean_array_uget_borrowed(v_bs_545_, v_i_544_);
v_snd_548_ = lean_ctor_get(v_v_547_, 1);
lean_inc(v_snd_548_);
v___x_549_ = lean_unsigned_to_nat(0u);
v_bs_x27_550_ = lean_array_uset(v_bs_545_, v_i_544_, v___x_549_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_add(v_i_544_, v___x_551_);
v___x_553_ = lean_array_uset(v_bs_x27_550_, v_i_544_, v_snd_548_);
v_i_544_ = v___x_552_;
v_bs_545_ = v___x_553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1___boxed(lean_object* v_sz_555_, lean_object* v_i_556_, lean_object* v_bs_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_555_);
lean_dec(v_sz_555_);
v_i_boxed_559_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v_sz_boxed_558_, v_i_boxed_559_, v_bs_557_);
return v_res_560_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2));
v___x_569_ = l_String_toRawSubstring_x27(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10));
v___x_587_ = l_String_toRawSubstring_x27(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Array_mkArray0(lean_box(0));
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__4));
v___x_610_ = l_Lean_mkAtom(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23));
v___x_613_ = l_String_toRawSubstring_x27(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32));
v___x_632_ = l_String_toRawSubstring_x27(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44));
v___x_662_ = l_String_toRawSubstring_x27(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51));
v___x_680_ = l_String_toRawSubstring_x27(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59));
v___x_699_ = l_String_toRawSubstring_x27(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67));
v___x_717_ = l_String_toRawSubstring_x27(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74));
v___x_734_ = l_String_toRawSubstring_x27(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(lean_object* v_x_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
lean_inc(v_x_750_);
v___x_754_ = l_Lean_Syntax_isOfKind(v_x_750_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v_x_750_);
v___x_755_ = lean_box(1);
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_a_752_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = l_Lean_Syntax_getArg(v_x_750_, v___x_757_);
lean_dec(v_x_750_);
v___x_759_ = ((lean_object*)(l_Lean_Json_jsonNull___closed__2));
lean_inc(v___x_758_);
v___x_760_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_Json_jsonTrue___closed__1));
lean_inc(v___x_758_);
v___x_762_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_Json_jsonFalse___closed__1));
lean_inc(v___x_758_);
v___x_764_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = ((lean_object*)(l_Lean_Json_json___00__closed__1));
lean_inc(v___x_758_);
v___x_767_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__1));
lean_inc(v___x_758_);
v___x_769_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___y_773_; 
v___x_770_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__1));
lean_inc(v___x_758_);
v___x_771_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v___y_825_; 
v___x_822_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__1));
lean_inc(v___x_758_);
v___x_823_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_Json_json_x7b___x7d___closed__1));
lean_inc(v___x_758_);
v___x_898_ = l_Lean_Syntax_isOfKind(v___x_758_, v___x_897_);
if (v___x_898_ == 0)
{
uint8_t v___x_899_; 
v___x_899_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v___x_758_);
v___x_900_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_900_;
}
else
{
lean_object* v_quotContext_901_; lean_object* v_currMacroScope_902_; lean_object* v_ref_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_quotContext_901_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_902_ = lean_ctor_get(v_a_751_, 2);
v_ref_903_ = lean_ctor_get(v_a_751_, 5);
v___x_904_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_905_ = l_Lean_SourceInfo_fromRef(v_ref_903_, v___x_898_);
v___x_906_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_907_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_908_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_902_);
lean_inc(v_quotContext_901_);
v___x_909_ = l_Lean_addMacroScope(v_quotContext_901_, v___x_908_, v_currMacroScope_902_);
v___x_910_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_905_, 2);
v___x_911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_911_, 0, v___x_905_);
lean_ctor_set(v___x_911_, 1, v___x_907_);
lean_ctor_set(v___x_911_, 2, v___x_909_);
lean_ctor_set(v___x_911_, 3, v___x_910_);
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_913_ = l_Lean_Syntax_node1(v___x_905_, v___x_912_, v___x_904_);
v___x_914_ = l_Lean_Syntax_node2(v___x_905_, v___x_906_, v___x_911_, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_a_752_);
return v___x_915_;
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_916_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_917_ = l_Lean_Syntax_getArgs(v___x_916_);
lean_dec(v___x_916_);
v___x_918_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31));
v___x_919_ = lean_array_get_size(v___x_917_);
v___x_920_ = lean_nat_dec_lt(v___x_765_, v___x_919_);
if (v___x_920_ == 0)
{
lean_dec_ref(v___x_917_);
v___y_825_ = v___x_918_;
goto v___jp_824_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_box(v___x_898_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_918_);
v___x_923_ = lean_nat_dec_le(v___x_919_, v___x_919_);
if (v___x_923_ == 0)
{
if (v___x_920_ == 0)
{
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_917_);
v___y_825_ = v___x_918_;
goto v___jp_824_;
}
else
{
size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v_snd_927_; 
v___x_924_ = ((size_t)0ULL);
v___x_925_ = lean_usize_of_nat(v___x_919_);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_898_, v___x_823_, v___x_917_, v___x_924_, v___x_925_, v___x_922_);
lean_dec_ref(v___x_917_);
v_snd_927_ = lean_ctor_get(v___x_926_, 1);
lean_inc(v_snd_927_);
lean_dec_ref(v___x_926_);
v___y_825_ = v_snd_927_;
goto v___jp_824_;
}
}
else
{
size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; lean_object* v_snd_931_; 
v___x_928_ = ((size_t)0ULL);
v___x_929_ = lean_usize_of_nat(v___x_919_);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_898_, v___x_823_, v___x_917_, v___x_928_, v___x_929_, v___x_922_);
lean_dec_ref(v___x_917_);
v_snd_931_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_snd_931_);
lean_dec_ref(v___x_930_);
v___y_825_ = v_snd_931_;
goto v___jp_824_;
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_932_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_933_ = l_Lean_Syntax_getArgs(v___x_932_);
lean_dec(v___x_932_);
v___x_934_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31));
v___x_935_ = lean_array_get_size(v___x_933_);
v___x_936_ = lean_nat_dec_lt(v___x_765_, v___x_935_);
if (v___x_936_ == 0)
{
lean_dec_ref(v___x_933_);
v___y_773_ = v___x_934_;
goto v___jp_772_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_937_ = lean_box(v___x_823_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_934_);
v___x_939_ = lean_nat_dec_le(v___x_935_, v___x_935_);
if (v___x_939_ == 0)
{
if (v___x_936_ == 0)
{
lean_dec_ref(v___x_938_);
lean_dec_ref(v___x_933_);
v___y_773_ = v___x_934_;
goto v___jp_772_;
}
else
{
size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; lean_object* v_snd_943_; 
v___x_940_ = ((size_t)0ULL);
v___x_941_ = lean_usize_of_nat(v___x_935_);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_823_, v___x_771_, v___x_933_, v___x_940_, v___x_941_, v___x_938_);
lean_dec_ref(v___x_933_);
v_snd_943_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_snd_943_);
lean_dec_ref(v___x_942_);
v___y_773_ = v_snd_943_;
goto v___jp_772_;
}
}
else
{
size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; lean_object* v_snd_947_; 
v___x_944_ = ((size_t)0ULL);
v___x_945_ = lean_usize_of_nat(v___x_935_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_823_, v___x_771_, v___x_933_, v___x_944_, v___x_945_, v___x_938_);
lean_dec_ref(v___x_933_);
v_snd_947_ = lean_ctor_get(v___x_946_, 1);
lean_inc(v_snd_947_);
lean_dec_ref(v___x_946_);
v___y_773_ = v_snd_947_;
goto v___jp_772_;
}
}
}
v___jp_824_:
{
size_t v_sz_826_; size_t v___x_827_; lean_object* v___x_828_; 
v_sz_826_ = lean_array_size(v___y_825_);
v___x_827_ = ((size_t)0ULL);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_826_, v___x_827_, v___y_825_);
if (lean_obj_tag(v___x_828_) == 0)
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v___x_758_);
v___x_830_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_830_;
}
else
{
lean_object* v_quotContext_831_; lean_object* v_currMacroScope_832_; lean_object* v_ref_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_quotContext_831_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_832_ = lean_ctor_get(v_a_751_, 2);
v_ref_833_ = lean_ctor_get(v_a_751_, 5);
v___x_834_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_835_ = l_Lean_SourceInfo_fromRef(v_ref_833_, v___x_823_);
v___x_836_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_837_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_838_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_832_);
lean_inc(v_quotContext_831_);
v___x_839_ = l_Lean_addMacroScope(v_quotContext_831_, v___x_838_, v_currMacroScope_832_);
v___x_840_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_835_, 2);
v___x_841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_841_, 0, v___x_835_);
lean_ctor_set(v___x_841_, 1, v___x_837_);
lean_ctor_set(v___x_841_, 2, v___x_839_);
lean_ctor_set(v___x_841_, 3, v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_843_ = l_Lean_Syntax_node1(v___x_835_, v___x_842_, v___x_834_);
v___x_844_ = l_Lean_Syntax_node2(v___x_835_, v___x_836_, v___x_841_, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_a_752_);
return v___x_845_;
}
}
else
{
lean_object* v_val_846_; size_t v_sz_847_; lean_object* v_vs_848_; lean_object* v_ks_849_; size_t v_sz_850_; lean_object* v___x_851_; 
lean_dec(v___x_758_);
v_val_846_ = lean_ctor_get(v___x_828_, 0);
lean_inc_n(v_val_846_, 2);
lean_dec_ref(v___x_828_);
v_sz_847_ = lean_array_size(v_val_846_);
v_vs_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v_sz_847_, v___x_827_, v_val_846_);
v_ks_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v_sz_847_, v___x_827_, v_val_846_);
v_sz_850_ = lean_array_size(v_ks_849_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(v_sz_850_, v___x_827_, v_ks_849_, v_a_752_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_887_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_a_853_ = lean_ctor_get(v___x_851_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_887_ == 0)
{
v___x_855_ = v___x_851_;
v_isShared_856_ = v_isSharedCheck_887_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_887_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_quotContext_857_; lean_object* v_currMacroScope_858_; lean_object* v_ref_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; size_t v_sz_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v_quotContext_857_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_858_ = lean_ctor_get(v_a_751_, 2);
v_ref_859_ = lean_ctor_get(v_a_751_, 5);
v___x_860_ = l_Lean_SourceInfo_fromRef(v_ref_859_, v___x_823_);
v___x_861_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_862_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24);
v___x_863_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26));
lean_inc_n(v_currMacroScope_858_, 2);
lean_inc_n(v_quotContext_857_, 2);
v___x_864_ = l_Lean_addMacroScope(v_quotContext_857_, v___x_863_, v_currMacroScope_858_);
v___x_865_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28));
lean_inc_n(v___x_860_, 7);
v___x_866_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_866_, 0, v___x_860_);
lean_ctor_set(v___x_866_, 1, v___x_862_);
lean_ctor_set(v___x_866_, 2, v___x_864_);
lean_ctor_set(v___x_866_, 3, v___x_865_);
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_868_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30));
v___x_869_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__2));
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_860_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
v___x_872_ = l_Array_zip___redArg(v_a_852_, v_vs_848_);
lean_dec_ref(v_vs_848_);
lean_dec(v_a_852_);
v_sz_873_ = lean_array_size(v___x_872_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v___x_860_, v_quotContext_857_, v_currMacroScope_858_, v_sz_873_, v___x_827_, v___x_872_);
v___x_875_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
v___x_876_ = l_Lean_mkSepArray(v___x_874_, v___x_875_);
lean_dec_ref(v___x_874_);
v___x_877_ = l_Array_append___redArg(v___x_871_, v___x_876_);
lean_dec_ref(v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_878_, 0, v___x_860_);
lean_ctor_set(v___x_878_, 1, v___x_867_);
lean_ctor_set(v___x_878_, 2, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__9));
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_860_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_Syntax_node3(v___x_860_, v___x_868_, v___x_870_, v___x_878_, v___x_880_);
v___x_882_ = l_Lean_Syntax_node1(v___x_860_, v___x_867_, v___x_881_);
v___x_883_ = l_Lean_Syntax_node2(v___x_860_, v___x_861_, v___x_866_, v___x_882_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_883_);
v___x_885_ = v___x_855_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_a_853_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v_vs_848_);
v_a_888_ = lean_ctor_get(v___x_851_, 0);
v_a_889_ = lean_ctor_get(v___x_851_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_851_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_inc(v_a_888_);
lean_dec(v___x_851_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_888_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
else
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = l_Lean_Syntax_getArg(v___x_758_, v___x_765_);
lean_inc(v___x_948_);
v___x_949_ = l_Lean_Syntax_matchesNull(v___x_948_, v___x_765_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; 
v___x_950_ = l_Lean_Syntax_matchesNull(v___x_948_, v___x_757_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_dec(v___x_758_);
v___x_952_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_952_;
}
else
{
lean_object* v_quotContext_953_; lean_object* v_currMacroScope_954_; lean_object* v_ref_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_quotContext_953_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_954_ = lean_ctor_get(v_a_751_, 2);
v_ref_955_ = lean_ctor_get(v_a_751_, 5);
v___x_956_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_957_ = l_Lean_SourceInfo_fromRef(v_ref_955_, v___x_950_);
v___x_958_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_959_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_960_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_954_);
lean_inc(v_quotContext_953_);
v___x_961_ = l_Lean_addMacroScope(v_quotContext_953_, v___x_960_, v_currMacroScope_954_);
v___x_962_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_957_, 2);
v___x_963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_963_, 0, v___x_957_);
lean_ctor_set(v___x_963_, 1, v___x_959_);
lean_ctor_set(v___x_963_, 2, v___x_961_);
lean_ctor_set(v___x_963_, 3, v___x_962_);
v___x_964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_965_ = l_Lean_Syntax_node1(v___x_957_, v___x_964_, v___x_956_);
v___x_966_ = l_Lean_Syntax_node2(v___x_957_, v___x_958_, v___x_963_, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v_a_752_);
return v___x_967_;
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_968_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_969_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_968_);
v___x_970_ = l_Lean_Syntax_isOfKind(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
uint8_t v___x_971_; 
lean_dec(v___x_968_);
v___x_971_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; 
lean_dec(v___x_758_);
v___x_972_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_972_;
}
else
{
lean_object* v_quotContext_973_; lean_object* v_currMacroScope_974_; lean_object* v_ref_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_quotContext_973_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_974_ = lean_ctor_get(v_a_751_, 2);
v_ref_975_ = lean_ctor_get(v_a_751_, 5);
v___x_976_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_977_ = l_Lean_SourceInfo_fromRef(v_ref_975_, v___x_970_);
v___x_978_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_979_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_980_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_974_);
lean_inc(v_quotContext_973_);
v___x_981_ = l_Lean_addMacroScope(v_quotContext_973_, v___x_980_, v_currMacroScope_974_);
v___x_982_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_977_, 2);
v___x_983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_983_, 0, v___x_977_);
lean_ctor_set(v___x_983_, 1, v___x_979_);
lean_ctor_set(v___x_983_, 2, v___x_981_);
lean_ctor_set(v___x_983_, 3, v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_985_ = l_Lean_Syntax_node1(v___x_977_, v___x_984_, v___x_976_);
v___x_986_ = l_Lean_Syntax_node2(v___x_977_, v___x_978_, v___x_983_, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_a_752_);
return v___x_987_;
}
}
else
{
lean_object* v_quotContext_988_; lean_object* v_currMacroScope_989_; lean_object* v_ref_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v___x_758_);
v_quotContext_988_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_989_ = lean_ctor_get(v_a_751_, 2);
v_ref_990_ = lean_ctor_get(v_a_751_, 5);
v___x_991_ = l_Lean_SourceInfo_fromRef(v_ref_990_, v___x_949_);
v___x_992_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_993_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_994_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_989_, 2);
lean_inc_n(v_quotContext_988_, 2);
v___x_995_ = l_Lean_addMacroScope(v_quotContext_988_, v___x_994_, v_currMacroScope_989_);
v___x_996_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_991_, 10);
v___x_997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_997_, 0, v___x_991_);
lean_ctor_set(v___x_997_, 1, v___x_993_);
lean_ctor_set(v___x_997_, 2, v___x_995_);
lean_ctor_set(v___x_997_, 3, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_999_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4));
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_991_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7));
v___x_1004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9);
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Lean_addMacroScope(v_quotContext_988_, v___x_1005_, v_currMacroScope_989_);
v___x_1007_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_1008_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1008_, 0, v___x_991_);
lean_ctor_set(v___x_1008_, 1, v___x_1004_);
lean_ctor_set(v___x_1008_, 2, v___x_1006_);
lean_ctor_set(v___x_1008_, 3, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node1(v___x_991_, v___x_1003_, v___x_1008_);
v___x_1010_ = l_Lean_Syntax_node2(v___x_991_, v___x_1000_, v___x_1002_, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1012_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_991_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node2(v___x_991_, v___x_1011_, v___x_1013_, v___x_968_);
v___x_1015_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_991_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_Syntax_node3(v___x_991_, v___x_999_, v___x_1010_, v___x_1014_, v___x_1016_);
v___x_1018_ = l_Lean_Syntax_node1(v___x_991_, v___x_998_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_node2(v___x_991_, v___x_992_, v___x_997_, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_a_752_);
return v___x_1020_;
}
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
lean_dec(v___x_948_);
v___x_1021_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_1022_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_1021_);
v___x_1023_ = l_Lean_Syntax_isOfKind(v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
uint8_t v___x_1024_; 
lean_dec(v___x_1021_);
v___x_1024_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec(v___x_758_);
v___x_1025_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1025_;
}
else
{
lean_object* v_quotContext_1026_; lean_object* v_currMacroScope_1027_; lean_object* v_ref_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_quotContext_1026_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1027_ = lean_ctor_get(v_a_751_, 2);
v_ref_1028_ = lean_ctor_get(v_a_751_, 5);
v___x_1029_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1030_ = l_Lean_SourceInfo_fromRef(v_ref_1028_, v___x_1023_);
v___x_1031_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1032_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1033_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1027_);
lean_inc(v_quotContext_1026_);
v___x_1034_ = l_Lean_addMacroScope(v_quotContext_1026_, v___x_1033_, v_currMacroScope_1027_);
v___x_1035_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1030_, 2);
v___x_1036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1030_);
lean_ctor_set(v___x_1036_, 1, v___x_1032_);
lean_ctor_set(v___x_1036_, 2, v___x_1034_);
lean_ctor_set(v___x_1036_, 3, v___x_1035_);
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1038_ = l_Lean_Syntax_node1(v___x_1030_, v___x_1037_, v___x_1029_);
v___x_1039_ = l_Lean_Syntax_node2(v___x_1030_, v___x_1031_, v___x_1036_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_a_752_);
return v___x_1040_;
}
}
else
{
lean_object* v_quotContext_1041_; lean_object* v_currMacroScope_1042_; lean_object* v_ref_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v___x_758_);
v_quotContext_1041_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1042_ = lean_ctor_get(v_a_751_, 2);
v_ref_1043_ = lean_ctor_get(v_a_751_, 5);
v___x_1044_ = l_Lean_SourceInfo_fromRef(v_ref_1043_, v___x_769_);
v___x_1045_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1046_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1047_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1042_);
lean_inc(v_quotContext_1041_);
v___x_1048_ = l_Lean_addMacroScope(v_quotContext_1041_, v___x_1047_, v_currMacroScope_1042_);
v___x_1049_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1044_, 2);
v___x_1050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1044_);
lean_ctor_set(v___x_1050_, 1, v___x_1046_);
lean_ctor_set(v___x_1050_, 2, v___x_1048_);
lean_ctor_set(v___x_1050_, 3, v___x_1049_);
v___x_1051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1052_ = l_Lean_Syntax_node1(v___x_1044_, v___x_1051_, v___x_1021_);
v___x_1053_ = l_Lean_Syntax_node2(v___x_1044_, v___x_1045_, v___x_1050_, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_a_752_);
return v___x_1054_;
}
}
}
v___jp_772_:
{
size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; 
v_sz_774_ = lean_array_size(v___y_773_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v_sz_774_, v___x_775_, v___y_773_);
if (lean_obj_tag(v___x_776_) == 0)
{
uint8_t v___x_777_; 
v___x_777_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec(v___x_758_);
v___x_778_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_778_;
}
else
{
lean_object* v_quotContext_779_; lean_object* v_currMacroScope_780_; lean_object* v_ref_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_quotContext_779_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_780_ = lean_ctor_get(v_a_751_, 2);
v_ref_781_ = lean_ctor_get(v_a_751_, 5);
v___x_782_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_783_ = l_Lean_SourceInfo_fromRef(v_ref_781_, v___x_771_);
v___x_784_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_785_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_786_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_780_);
lean_inc(v_quotContext_779_);
v___x_787_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_786_, v_currMacroScope_780_);
v___x_788_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_783_, 2);
v___x_789_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_789_, 0, v___x_783_);
lean_ctor_set(v___x_789_, 1, v___x_785_);
lean_ctor_set(v___x_789_, 2, v___x_787_);
lean_ctor_set(v___x_789_, 3, v___x_788_);
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_791_ = l_Lean_Syntax_node1(v___x_783_, v___x_790_, v___x_782_);
v___x_792_ = l_Lean_Syntax_node2(v___x_783_, v___x_784_, v___x_789_, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_752_);
return v___x_793_;
}
}
else
{
lean_object* v_val_794_; lean_object* v_quotContext_795_; lean_object* v_currMacroScope_796_; lean_object* v_ref_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; size_t v_sz_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec(v___x_758_);
v_val_794_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_val_794_);
lean_dec_ref(v___x_776_);
v_quotContext_795_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_796_ = lean_ctor_get(v_a_751_, 2);
v_ref_797_ = lean_ctor_get(v_a_751_, 5);
v___x_798_ = l_Lean_SourceInfo_fromRef(v_ref_797_, v___x_771_);
v___x_799_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_800_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11);
v___x_801_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13));
lean_inc(v_currMacroScope_796_);
lean_inc(v_quotContext_795_);
v___x_802_ = l_Lean_addMacroScope(v_quotContext_795_, v___x_801_, v_currMacroScope_796_);
v___x_803_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17));
lean_inc_n(v___x_798_, 7);
v___x_804_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_804_, 0, v___x_798_);
lean_ctor_set(v___x_804_, 1, v___x_800_);
lean_ctor_set(v___x_804_, 2, v___x_802_);
lean_ctor_set(v___x_804_, 3, v___x_803_);
v___x_805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_806_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19));
v___x_807_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20));
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_798_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
v_sz_810_ = lean_array_size(v_val_794_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_798_, v_sz_810_, v___x_775_, v_val_794_);
v___x_812_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
v___x_813_ = l_Lean_mkSepArray(v___x_811_, v___x_812_);
lean_dec_ref(v___x_811_);
v___x_814_ = l_Array_append___redArg(v___x_809_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_815_, 0, v___x_798_);
lean_ctor_set(v___x_815_, 1, v___x_805_);
lean_ctor_set(v___x_815_, 2, v___x_814_);
v___x_816_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__9));
v___x_817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_798_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Syntax_node3(v___x_798_, v___x_806_, v___x_808_, v___x_815_, v___x_817_);
v___x_819_ = l_Lean_Syntax_node1(v___x_798_, v___x_805_, v___x_818_);
v___x_820_ = l_Lean_Syntax_node2(v___x_798_, v___x_799_, v___x_804_, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_a_752_);
return v___x_821_;
}
}
}
else
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = l_Lean_Syntax_getArg(v___x_758_, v___x_765_);
lean_inc(v___x_1055_);
v___x_1056_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_765_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_757_);
if (v___x_1057_ == 0)
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v___x_758_);
v___x_1059_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1059_;
}
else
{
lean_object* v_quotContext_1060_; lean_object* v_currMacroScope_1061_; lean_object* v_ref_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_quotContext_1060_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1061_ = lean_ctor_get(v_a_751_, 2);
v_ref_1062_ = lean_ctor_get(v_a_751_, 5);
v___x_1063_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1064_ = l_Lean_SourceInfo_fromRef(v_ref_1062_, v___x_1057_);
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
v___x_1071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1072_ = l_Lean_Syntax_node1(v___x_1064_, v___x_1071_, v___x_1063_);
v___x_1073_ = l_Lean_Syntax_node2(v___x_1064_, v___x_1065_, v___x_1070_, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_752_);
return v___x_1074_;
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_1076_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1075_);
v___x_1077_ = l_Lean_Syntax_isOfKind(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
uint8_t v___x_1078_; 
lean_dec(v___x_1075_);
v___x_1078_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v___x_758_);
v___x_1079_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1079_;
}
else
{
lean_object* v_quotContext_1080_; lean_object* v_currMacroScope_1081_; lean_object* v_ref_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_quotContext_1080_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1081_ = lean_ctor_get(v_a_751_, 2);
v_ref_1082_ = lean_ctor_get(v_a_751_, 5);
v___x_1083_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1084_ = l_Lean_SourceInfo_fromRef(v_ref_1082_, v___x_1077_);
v___x_1085_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1086_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1087_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1081_);
lean_inc(v_quotContext_1080_);
v___x_1088_ = l_Lean_addMacroScope(v_quotContext_1080_, v___x_1087_, v_currMacroScope_1081_);
v___x_1089_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1084_, 2);
v___x_1090_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1084_);
lean_ctor_set(v___x_1090_, 1, v___x_1086_);
lean_ctor_set(v___x_1090_, 2, v___x_1088_);
lean_ctor_set(v___x_1090_, 3, v___x_1089_);
v___x_1091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1092_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1091_, v___x_1083_);
v___x_1093_ = l_Lean_Syntax_node2(v___x_1084_, v___x_1085_, v___x_1090_, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_a_752_);
return v___x_1094_;
}
}
else
{
lean_object* v_quotContext_1095_; lean_object* v_currMacroScope_1096_; lean_object* v_ref_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v___x_758_);
v_quotContext_1095_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1096_ = lean_ctor_get(v_a_751_, 2);
v_ref_1097_ = lean_ctor_get(v_a_751_, 5);
v___x_1098_ = l_Lean_SourceInfo_fromRef(v_ref_1097_, v___x_1056_);
v___x_1099_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1100_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1101_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_1096_, 2);
lean_inc_n(v_quotContext_1095_, 2);
v___x_1102_ = l_Lean_addMacroScope(v_quotContext_1095_, v___x_1101_, v_currMacroScope_1096_);
v___x_1103_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1098_, 10);
v___x_1104_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1098_);
lean_ctor_set(v___x_1104_, 1, v___x_1100_);
lean_ctor_set(v___x_1104_, 2, v___x_1102_);
lean_ctor_set(v___x_1104_, 3, v___x_1103_);
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1106_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4));
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5));
v___x_1109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1098_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7));
v___x_1111_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9);
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Lean_addMacroScope(v_quotContext_1095_, v___x_1112_, v_currMacroScope_1096_);
v___x_1114_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_1115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1098_);
lean_ctor_set(v___x_1115_, 1, v___x_1111_);
lean_ctor_set(v___x_1115_, 2, v___x_1113_);
lean_ctor_set(v___x_1115_, 3, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node1(v___x_1098_, v___x_1110_, v___x_1115_);
v___x_1117_ = l_Lean_Syntax_node2(v___x_1098_, v___x_1107_, v___x_1109_, v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1119_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1098_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_node2(v___x_1098_, v___x_1118_, v___x_1120_, v___x_1075_);
v___x_1122_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1098_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node3(v___x_1098_, v___x_1106_, v___x_1117_, v___x_1121_, v___x_1123_);
v___x_1125_ = l_Lean_Syntax_node1(v___x_1098_, v___x_1105_, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node2(v___x_1098_, v___x_1099_, v___x_1104_, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v_a_752_);
return v___x_1127_;
}
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
lean_dec(v___x_1055_);
v___x_1128_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_1129_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1128_);
v___x_1130_ = l_Lean_Syntax_isOfKind(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; 
lean_dec(v___x_1128_);
v___x_1131_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec(v___x_758_);
v___x_1132_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1132_;
}
else
{
lean_object* v_quotContext_1133_; lean_object* v_currMacroScope_1134_; lean_object* v_ref_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_quotContext_1133_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1134_ = lean_ctor_get(v_a_751_, 2);
v_ref_1135_ = lean_ctor_get(v_a_751_, 5);
v___x_1136_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1137_ = l_Lean_SourceInfo_fromRef(v_ref_1135_, v___x_1130_);
v___x_1138_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1139_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1140_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1134_);
lean_inc(v_quotContext_1133_);
v___x_1141_ = l_Lean_addMacroScope(v_quotContext_1133_, v___x_1140_, v_currMacroScope_1134_);
v___x_1142_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1137_, 2);
v___x_1143_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1137_);
lean_ctor_set(v___x_1143_, 1, v___x_1139_);
lean_ctor_set(v___x_1143_, 2, v___x_1141_);
lean_ctor_set(v___x_1143_, 3, v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1145_ = l_Lean_Syntax_node1(v___x_1137_, v___x_1144_, v___x_1136_);
v___x_1146_ = l_Lean_Syntax_node2(v___x_1137_, v___x_1138_, v___x_1143_, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_a_752_);
return v___x_1147_;
}
}
else
{
lean_object* v_quotContext_1148_; lean_object* v_currMacroScope_1149_; lean_object* v_ref_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v___x_758_);
v_quotContext_1148_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1149_ = lean_ctor_get(v_a_751_, 2);
v_ref_1150_ = lean_ctor_get(v_a_751_, 5);
v___x_1151_ = l_Lean_SourceInfo_fromRef(v_ref_1150_, v___x_767_);
v___x_1152_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1153_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1154_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1149_);
lean_inc(v_quotContext_1148_);
v___x_1155_ = l_Lean_addMacroScope(v_quotContext_1148_, v___x_1154_, v_currMacroScope_1149_);
v___x_1156_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1151_, 2);
v___x_1157_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1151_);
lean_ctor_set(v___x_1157_, 1, v___x_1153_);
lean_ctor_set(v___x_1157_, 2, v___x_1155_);
lean_ctor_set(v___x_1157_, 3, v___x_1156_);
v___x_1158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1159_ = l_Lean_Syntax_node1(v___x_1151_, v___x_1158_, v___x_1128_);
v___x_1160_ = l_Lean_Syntax_node2(v___x_1151_, v___x_1152_, v___x_1157_, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_a_752_);
return v___x_1161_;
}
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = l_Lean_Syntax_getArg(v___x_758_, v___x_765_);
v___x_1163_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v___x_1162_);
v___x_1164_ = l_Lean_Syntax_isOfKind(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint8_t v___x_1165_; 
lean_dec(v___x_1162_);
v___x_1165_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec(v___x_758_);
v___x_1166_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1166_;
}
else
{
lean_object* v_quotContext_1167_; lean_object* v_currMacroScope_1168_; lean_object* v_ref_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_quotContext_1167_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1168_ = lean_ctor_get(v_a_751_, 2);
v_ref_1169_ = lean_ctor_get(v_a_751_, 5);
v___x_1170_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1171_ = l_Lean_SourceInfo_fromRef(v_ref_1169_, v___x_1164_);
v___x_1172_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1173_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1174_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1168_);
lean_inc(v_quotContext_1167_);
v___x_1175_ = l_Lean_addMacroScope(v_quotContext_1167_, v___x_1174_, v_currMacroScope_1168_);
v___x_1176_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1171_, 2);
v___x_1177_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1171_);
lean_ctor_set(v___x_1177_, 1, v___x_1173_);
lean_ctor_set(v___x_1177_, 2, v___x_1175_);
lean_ctor_set(v___x_1177_, 3, v___x_1176_);
v___x_1178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1179_ = l_Lean_Syntax_node1(v___x_1171_, v___x_1178_, v___x_1170_);
v___x_1180_ = l_Lean_Syntax_node2(v___x_1171_, v___x_1172_, v___x_1177_, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v_a_752_);
return v___x_1181_;
}
}
else
{
lean_object* v_quotContext_1182_; lean_object* v_currMacroScope_1183_; lean_object* v_ref_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v___x_758_);
v_quotContext_1182_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1183_ = lean_ctor_get(v_a_751_, 2);
v_ref_1184_ = lean_ctor_get(v_a_751_, 5);
v___x_1185_ = l_Lean_SourceInfo_fromRef(v_ref_1184_, v___x_764_);
v___x_1186_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1187_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45);
v___x_1188_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46));
lean_inc(v_currMacroScope_1183_);
lean_inc(v_quotContext_1182_);
v___x_1189_ = l_Lean_addMacroScope(v_quotContext_1182_, v___x_1188_, v_currMacroScope_1183_);
v___x_1190_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50));
lean_inc_n(v___x_1185_, 2);
v___x_1191_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1185_);
lean_ctor_set(v___x_1191_, 1, v___x_1187_);
lean_ctor_set(v___x_1191_, 2, v___x_1189_);
lean_ctor_set(v___x_1191_, 3, v___x_1190_);
v___x_1192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1193_ = l_Lean_Syntax_node1(v___x_1185_, v___x_1192_, v___x_1162_);
v___x_1194_ = l_Lean_Syntax_node2(v___x_1185_, v___x_1186_, v___x_1191_, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v_a_752_);
return v___x_1195_;
}
}
}
else
{
lean_object* v_quotContext_1196_; lean_object* v_currMacroScope_1197_; lean_object* v_ref_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec(v___x_758_);
v_quotContext_1196_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1197_ = lean_ctor_get(v_a_751_, 2);
v_ref_1198_ = lean_ctor_get(v_a_751_, 5);
v___x_1199_ = l_Lean_SourceInfo_fromRef(v_ref_1198_, v___x_762_);
v___x_1200_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1201_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1202_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1197_, 2);
lean_inc_n(v_quotContext_1196_, 2);
v___x_1203_ = l_Lean_addMacroScope(v_quotContext_1196_, v___x_1202_, v_currMacroScope_1197_);
v___x_1204_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1199_, 3);
v___x_1205_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1199_);
lean_ctor_set(v___x_1205_, 1, v___x_1201_);
lean_ctor_set(v___x_1205_, 2, v___x_1203_);
lean_ctor_set(v___x_1205_, 3, v___x_1204_);
v___x_1206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1207_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60);
v___x_1208_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62));
v___x_1209_ = l_Lean_addMacroScope(v_quotContext_1196_, v___x_1208_, v_currMacroScope_1197_);
v___x_1210_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66));
v___x_1211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1199_);
lean_ctor_set(v___x_1211_, 1, v___x_1207_);
lean_ctor_set(v___x_1211_, 2, v___x_1209_);
lean_ctor_set(v___x_1211_, 3, v___x_1210_);
v___x_1212_ = l_Lean_Syntax_node1(v___x_1199_, v___x_1206_, v___x_1211_);
v___x_1213_ = l_Lean_Syntax_node2(v___x_1199_, v___x_1200_, v___x_1205_, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v_a_752_);
return v___x_1214_;
}
}
else
{
lean_object* v_quotContext_1215_; lean_object* v_currMacroScope_1216_; lean_object* v_ref_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v___x_758_);
v_quotContext_1215_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1216_ = lean_ctor_get(v_a_751_, 2);
v_ref_1217_ = lean_ctor_get(v_a_751_, 5);
v___x_1218_ = l_Lean_SourceInfo_fromRef(v_ref_1217_, v___x_760_);
v___x_1219_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1220_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1221_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1216_, 2);
lean_inc_n(v_quotContext_1215_, 2);
v___x_1222_ = l_Lean_addMacroScope(v_quotContext_1215_, v___x_1221_, v_currMacroScope_1216_);
v___x_1223_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1218_, 3);
v___x_1224_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1218_);
lean_ctor_set(v___x_1224_, 1, v___x_1220_);
lean_ctor_set(v___x_1224_, 2, v___x_1222_);
lean_ctor_set(v___x_1224_, 3, v___x_1223_);
v___x_1225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0));
v___x_1226_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68);
v___x_1227_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69));
v___x_1228_ = l_Lean_addMacroScope(v_quotContext_1215_, v___x_1227_, v_currMacroScope_1216_);
v___x_1229_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73));
v___x_1230_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1218_);
lean_ctor_set(v___x_1230_, 1, v___x_1226_);
lean_ctor_set(v___x_1230_, 2, v___x_1228_);
lean_ctor_set(v___x_1230_, 3, v___x_1229_);
v___x_1231_ = l_Lean_Syntax_node1(v___x_1218_, v___x_1225_, v___x_1230_);
v___x_1232_ = l_Lean_Syntax_node2(v___x_1218_, v___x_1219_, v___x_1224_, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v_a_752_);
return v___x_1233_;
}
}
else
{
lean_object* v_quotContext_1234_; lean_object* v_currMacroScope_1235_; lean_object* v_ref_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v___x_758_);
v_quotContext_1234_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1235_ = lean_ctor_get(v_a_751_, 2);
v_ref_1236_ = lean_ctor_get(v_a_751_, 5);
v___x_1237_ = 0;
v___x_1238_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1237_);
v___x_1239_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75);
v___x_1240_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76));
lean_inc(v_currMacroScope_1235_);
lean_inc(v_quotContext_1234_);
v___x_1241_ = l_Lean_addMacroScope(v_quotContext_1234_, v___x_1240_, v_currMacroScope_1235_);
v___x_1242_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80));
v___x_1243_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1238_);
lean_ctor_set(v___x_1243_, 1, v___x_1239_);
lean_ctor_set(v___x_1243_, 2, v___x_1241_);
lean_ctor_set(v___x_1243_, 3, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_a_752_);
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___boxed(lean_object* v_x_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(v_x_1245_, v_a_1246_, v_a_1247_);
lean_dec_ref(v_a_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(size_t v_sz_1249_, size_t v_i_1250_, lean_object* v_bs_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(v_sz_1249_, v_i_1250_, v_bs_1251_, v___y_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(lean_object* v_sz_1255_, lean_object* v_i_1256_, lean_object* v_bs_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
size_t v_sz_boxed_1260_; size_t v_i_boxed_1261_; lean_object* v_res_1262_; 
v_sz_boxed_1260_ = lean_unbox_usize(v_sz_1255_);
lean_dec(v_sz_1255_);
v_i_boxed_1261_ = lean_unbox_usize(v_i_1256_);
lean_dec(v_i_1256_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_boxed_1260_, v_i_boxed_1261_, v_bs_1257_, v___y_1258_, v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1262_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Elab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
