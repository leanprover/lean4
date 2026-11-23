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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* l_Array_mkArray0___redArg();
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Category_json(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(size_t v_sz_275_, size_t v_i_276_, lean_object* v_bs_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_lt(v_i_276_, v_sz_275_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_bs_277_);
return v___x_279_;
}
else
{
lean_object* v_v_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_v_280_ = lean_array_uget(v_bs_277_, v_i_276_);
v___x_281_ = ((lean_object*)(l_Lean_Json_jsonField___closed__1));
lean_inc(v_v_280_);
v___x_282_ = l_Lean_Syntax_isOfKind(v_v_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
lean_dec(v_v_280_);
lean_dec_ref(v_bs_277_);
v___x_283_ = lean_box(0);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v_ks_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v_ks_285_ = l_Lean_Syntax_getArg(v_v_280_, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_ks_285_);
v___x_287_ = l_Lean_Syntax_isOfKind(v_ks_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec(v_ks_285_);
lean_dec(v_v_280_);
lean_dec_ref(v_bs_277_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v_bs_x27_289_; lean_object* v___x_290_; lean_object* v_vs_291_; lean_object* v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v_bs_x27_289_ = lean_array_uset(v_bs_277_, v_i_276_, v___x_284_);
v___x_290_ = lean_unsigned_to_nat(2u);
v_vs_291_ = l_Lean_Syntax_getArg(v_v_280_, v___x_290_);
lean_dec(v_v_280_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_ks_285_);
lean_ctor_set(v___x_292_, 1, v_vs_291_);
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_add(v_i_276_, v___x_293_);
v___x_295_ = lean_array_uset(v_bs_x27_289_, v_i_276_, v___x_292_);
v_i_276_ = v___x_294_;
v_bs_277_ = v___x_295_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(lean_object* v_sz_297_, lean_object* v_i_298_, lean_object* v_bs_299_){
_start:
{
size_t v_sz_boxed_300_; size_t v_i_boxed_301_; lean_object* v_res_302_; 
v_sz_boxed_300_ = lean_unbox_usize(v_sz_297_);
lean_dec(v_sz_297_);
v_i_boxed_301_ = lean_unbox_usize(v_i_298_);
lean_dec(v_i_298_);
v_res_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v_sz_boxed_300_, v_i_boxed_301_, v_bs_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(size_t v_sz_303_, size_t v_i_304_, lean_object* v_bs_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = lean_usize_dec_lt(v_i_304_, v_sz_303_);
if (v___x_306_ == 0)
{
return v_bs_305_;
}
else
{
lean_object* v_v_307_; lean_object* v_fst_308_; lean_object* v___x_309_; lean_object* v_bs_x27_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v_v_307_ = lean_array_uget_borrowed(v_bs_305_, v_i_304_);
v_fst_308_ = lean_ctor_get(v_v_307_, 0);
lean_inc(v_fst_308_);
v___x_309_ = lean_unsigned_to_nat(0u);
v_bs_x27_310_ = lean_array_uset(v_bs_305_, v_i_304_, v___x_309_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_i_304_, v___x_311_);
v___x_313_ = lean_array_uset(v_bs_x27_310_, v_i_304_, v_fst_308_);
v_i_304_ = v___x_312_;
v_bs_305_ = v___x_313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(lean_object* v_sz_315_, lean_object* v_i_316_, lean_object* v_bs_317_){
_start:
{
size_t v_sz_boxed_318_; size_t v_i_boxed_319_; lean_object* v_res_320_; 
v_sz_boxed_318_ = lean_unbox_usize(v_sz_315_);
lean_dec(v_sz_315_);
v_i_boxed_319_ = lean_unbox_usize(v_i_316_);
lean_dec(v_i_316_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v_sz_boxed_318_, v_i_boxed_319_, v_bs_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(size_t v_sz_321_, size_t v_i_322_, lean_object* v_bs_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_lt(v_i_322_, v_sz_321_);
if (v___x_324_ == 0)
{
return v_bs_323_;
}
else
{
lean_object* v_v_325_; lean_object* v_snd_326_; lean_object* v___x_327_; lean_object* v_bs_x27_328_; size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v_v_325_ = lean_array_uget_borrowed(v_bs_323_, v_i_322_);
v_snd_326_ = lean_ctor_get(v_v_325_, 1);
lean_inc(v_snd_326_);
v___x_327_ = lean_unsigned_to_nat(0u);
v_bs_x27_328_ = lean_array_uset(v_bs_323_, v_i_322_, v___x_327_);
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_322_, v___x_329_);
v___x_331_ = lean_array_uset(v_bs_x27_328_, v_i_322_, v_snd_326_);
v_i_322_ = v___x_330_;
v_bs_323_ = v___x_331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(lean_object* v_sz_333_, lean_object* v_i_334_, lean_object* v_bs_335_){
_start:
{
size_t v_sz_boxed_336_; size_t v_i_boxed_337_; lean_object* v_res_338_; 
v_sz_boxed_336_ = lean_unbox_usize(v_sz_333_);
lean_dec(v_sz_333_);
v_i_boxed_337_ = lean_unbox_usize(v_i_334_);
lean_dec(v_i_334_);
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_boxed_336_, v_i_boxed_337_, v_bs_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___redArg(size_t v_sz_339_, size_t v_i_340_, lean_object* v_bs_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_usize_dec_lt(v_i_340_, v_sz_339_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_bs_341_);
lean_ctor_set(v___x_344_, 1, v___y_342_);
return v___x_344_;
}
else
{
lean_object* v_v_345_; lean_object* v___x_346_; lean_object* v_bs_x27_347_; lean_object* v_a_349_; lean_object* v_a_350_; lean_object* v___y_356_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_v_345_ = lean_array_uget(v_bs_341_, v_i_340_);
v___x_346_ = lean_unsigned_to_nat(0u);
v_bs_x27_347_ = lean_array_uset(v_bs_341_, v_i_340_, v___x_346_);
v___x_368_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_v_345_);
v___x_369_ = l_Lean_Syntax_isOfKind(v_v_345_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_v_345_);
v___x_370_ = l_Lean_Macro_throwUnsupported___redArg(v___y_342_);
v___y_356_ = v___x_370_;
goto v___jp_355_;
}
else
{
lean_object* v_k_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_k_371_ = l_Lean_Syntax_getArg(v_v_345_, v___x_346_);
lean_dec(v_v_345_);
v___x_372_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__5));
lean_inc(v_k_371_);
v___x_373_ = l_Lean_Syntax_isOfKind(v_k_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v_k_371_);
v___x_375_ = l_Lean_Syntax_isOfKind(v_k_371_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v_k_371_);
v___x_376_ = l_Lean_Macro_throwUnsupported___redArg(v___y_342_);
v___y_356_ = v___x_376_;
goto v___jp_355_;
}
else
{
v_a_349_ = v_k_371_;
v_a_350_ = v___y_342_;
goto v___jp_348_;
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = l_Lean_TSyntax_getId(v_k_371_);
lean_dec(v_k_371_);
v___x_378_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_377_, v___x_369_);
v___x_379_ = lean_box(2);
v___x_380_ = l_Lean_Syntax_mkStrLit(v___x_378_, v___x_379_);
v_a_349_ = v___x_380_;
v_a_350_ = v___y_342_;
goto v___jp_348_;
}
}
v___jp_348_:
{
size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_add(v_i_340_, v___x_351_);
v___x_353_ = lean_array_uset(v_bs_x27_347_, v_i_340_, v_a_349_);
v_i_340_ = v___x_352_;
v_bs_341_ = v___x_353_;
v___y_342_ = v_a_350_;
goto _start;
}
v___jp_355_:
{
if (lean_obj_tag(v___y_356_) == 0)
{
lean_object* v_a_357_; lean_object* v_a_358_; 
v_a_357_ = lean_ctor_get(v___y_356_, 0);
lean_inc(v_a_357_);
v_a_358_ = lean_ctor_get(v___y_356_, 1);
lean_inc(v_a_358_);
lean_dec_ref_known(v___y_356_, 2);
v_a_349_ = v_a_357_;
v_a_350_ = v_a_358_;
goto v___jp_348_;
}
else
{
lean_object* v_a_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v_bs_x27_347_);
v_a_359_ = lean_ctor_get(v___y_356_, 0);
v_a_360_ = lean_ctor_get(v___y_356_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___y_356_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___y_356_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_inc(v_a_359_);
lean_dec(v___y_356_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_359_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___redArg___boxed(lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_bs_383_, lean_object* v___y_384_){
_start:
{
size_t v_sz_boxed_385_; size_t v_i_boxed_386_; lean_object* v_res_387_; 
v_sz_boxed_385_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_386_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___redArg(v_sz_boxed_385_, v_i_boxed_386_, v_bs_383_, v___y_384_);
return v_res_387_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__8));
v___x_408_ = l_String_toRawSubstring_x27(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, size_t v_sz_421_, size_t v_i_422_, lean_object* v_bs_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_lt(v_i_422_, v_sz_421_);
if (v___x_424_ == 0)
{
lean_dec(v___x_420_);
lean_dec(v___x_419_);
lean_dec(v___x_418_);
return v_bs_423_;
}
else
{
lean_object* v_v_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_463_; 
v_v_425_ = lean_array_uget(v_bs_423_, v_i_422_);
v_fst_426_ = lean_ctor_get(v_v_425_, 0);
v_snd_427_ = lean_ctor_get(v_v_425_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_v_425_);
if (v_isSharedCheck_463_ == 0)
{
v___x_429_ = v_v_425_;
v_isShared_430_ = v_isSharedCheck_463_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v_v_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_463_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_bs_x27_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_431_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v___x_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_433_ = lean_unsigned_to_nat(0u);
v_bs_x27_434_ = lean_array_uset(v_bs_423_, v_i_422_, v___x_433_);
v___x_435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2));
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
lean_inc(v___x_418_);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 2);
lean_ctor_set(v___x_429_, 1, v___x_437_);
lean_ctor_set(v___x_429_, 0, v___x_418_);
v___x_439_ = v___x_429_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_462_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v___x_440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_441_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_442_ = lean_box(0);
lean_inc(v___x_420_);
lean_inc(v___x_419_);
v___x_443_ = l_Lean_addMacroScope(v___x_419_, v___x_442_, v___x_420_);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__12));
lean_inc_n(v___x_418_, 10);
v___x_445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_445_, 0, v___x_418_);
lean_ctor_set(v___x_445_, 1, v___x_441_);
lean_ctor_set(v___x_445_, 2, v___x_443_);
lean_ctor_set(v___x_445_, 3, v___x_444_);
v___x_446_ = l_Lean_Syntax_node1(v___x_418_, v___x_440_, v___x_445_);
v___x_447_ = l_Lean_Syntax_node2(v___x_418_, v___x_436_, v___x_439_, v___x_446_);
v___x_448_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__4));
v___x_449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_418_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13));
v___x_451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_418_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = l_Lean_Syntax_node2(v___x_418_, v___x_431_, v___x_451_, v_snd_427_);
v___x_453_ = l_Lean_Syntax_node1(v___x_418_, v___x_432_, v___x_452_);
v___x_454_ = l_Lean_Syntax_node3(v___x_418_, v___x_432_, v_fst_426_, v___x_449_, v___x_453_);
v___x_455_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_418_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_Syntax_node3(v___x_418_, v___x_435_, v___x_447_, v___x_454_, v___x_456_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_422_, v___x_458_);
v___x_460_ = lean_array_uset(v_bs_x27_434_, v_i_422_, v___x_457_);
v_i_422_ = v___x_459_;
v_bs_423_ = v___x_460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___boxed(lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v_sz_467_, lean_object* v_i_468_, lean_object* v_bs_469_){
_start:
{
size_t v_sz_boxed_470_; size_t v_i_boxed_471_; lean_object* v_res_472_; 
v_sz_boxed_470_ = lean_unbox_usize(v_sz_467_);
lean_dec(v_sz_467_);
v_i_boxed_471_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v___x_464_, v___x_465_, v___x_466_, v_sz_boxed_470_, v_i_boxed_471_, v_bs_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(size_t v_sz_473_, size_t v_i_474_, lean_object* v_bs_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_bs_475_);
return v___x_477_;
}
else
{
lean_object* v_v_478_; lean_object* v___x_479_; lean_object* v_bs_x27_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v_v_478_ = lean_array_uget(v_bs_475_, v_i_474_);
v___x_479_ = lean_unsigned_to_nat(0u);
v_bs_x27_480_ = lean_array_uset(v_bs_475_, v_i_474_, v___x_479_);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_add(v_i_474_, v___x_481_);
v___x_483_ = lean_array_uset(v_bs_x27_480_, v_i_474_, v_v_478_);
v_i_474_ = v___x_482_;
v_bs_475_ = v___x_483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0___boxed(lean_object* v_sz_485_, lean_object* v_i_486_, lean_object* v_bs_487_){
_start:
{
size_t v_sz_boxed_488_; size_t v_i_boxed_489_; lean_object* v_res_490_; 
v_sz_boxed_488_ = lean_unbox_usize(v_sz_485_);
lean_dec(v_sz_485_);
v_i_boxed_489_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_boxed_488_, v_i_boxed_489_, v_bs_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(lean_object* v___x_491_, size_t v_sz_492_, size_t v_i_493_, lean_object* v_bs_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_495_ == 0)
{
lean_dec(v___x_491_);
return v_bs_494_;
}
else
{
lean_object* v___x_496_; lean_object* v_v_497_; lean_object* v___x_498_; lean_object* v_bs_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_496_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v_v_497_ = lean_array_uget(v_bs_494_, v_i_493_);
v___x_498_ = lean_unsigned_to_nat(0u);
v_bs_x27_499_ = lean_array_uset(v_bs_494_, v_i_493_, v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13));
lean_inc_n(v___x_491_, 2);
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_491_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_Syntax_node2(v___x_491_, v___x_496_, v___x_501_, v_v_497_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_493_, v___x_503_);
v___x_505_ = lean_array_uset(v_bs_x27_499_, v_i_493_, v___x_502_);
v_i_493_ = v___x_504_;
v_bs_494_ = v___x_505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1___boxed(lean_object* v___x_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v___x_507_, v_sz_boxed_511_, v_i_boxed_512_, v_bs_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(uint8_t v___x_514_, uint8_t v___x_515_, lean_object* v_as_516_, size_t v_i_517_, size_t v_stop_518_, lean_object* v_b_519_){
_start:
{
lean_object* v___y_521_; uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_eq(v_i_517_, v_stop_518_);
if (v___x_525_ == 0)
{
lean_object* v_fst_526_; uint8_t v___x_527_; 
v_fst_526_ = lean_ctor_get(v_b_519_, 0);
v___x_527_ = lean_unbox(v_fst_526_);
if (v___x_527_ == 0)
{
lean_object* v_snd_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_snd_528_ = lean_ctor_get(v_b_519_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v_b_519_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_b_519_, 0);
lean_dec(v_unused_537_);
v___x_530_ = v_b_519_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snd_528_);
lean_dec(v_b_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_box(v___x_514_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_snd_528_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
v___y_521_ = v___x_534_;
goto v___jp_520_;
}
}
}
else
{
lean_object* v_snd_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_548_; 
v_snd_538_ = lean_ctor_get(v_b_519_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_b_519_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_b_519_, 0);
lean_dec(v_unused_549_);
v___x_540_ = v_b_519_;
v_isShared_541_ = v_isSharedCheck_548_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snd_538_);
lean_dec(v_b_519_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_548_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_542_ = lean_array_uget_borrowed(v_as_516_, v_i_517_);
lean_inc(v___x_542_);
v___x_543_ = lean_array_push(v_snd_538_, v___x_542_);
v___x_544_ = lean_box(v___x_515_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_543_);
lean_ctor_set(v___x_540_, 0, v___x_544_);
v___x_546_ = v___x_540_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_543_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v___y_521_ = v___x_546_;
goto v___jp_520_;
}
}
}
}
else
{
return v_b_519_;
}
v___jp_520_:
{
size_t v___x_522_; size_t v___x_523_; 
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_i_517_, v___x_522_);
v_i_517_ = v___x_523_;
v_b_519_ = v___y_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7___boxed(lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v_as_552_, lean_object* v_i_553_, lean_object* v_stop_554_, lean_object* v_b_555_){
_start:
{
uint8_t v___x_32528__boxed_556_; uint8_t v___x_32529__boxed_557_; size_t v_i_boxed_558_; size_t v_stop_boxed_559_; lean_object* v_res_560_; 
v___x_32528__boxed_556_ = lean_unbox(v___x_550_);
v___x_32529__boxed_557_ = lean_unbox(v___x_551_);
v_i_boxed_558_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_stop_boxed_559_ = lean_unbox_usize(v_stop_554_);
lean_dec(v_stop_554_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_32528__boxed_556_, v___x_32529__boxed_557_, v_as_552_, v_i_boxed_558_, v_stop_boxed_559_, v_b_555_);
lean_dec_ref(v_as_552_);
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
v___x_608_ = l_Array_mkArray0___redArg();
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
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
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
lean_object* v___x_921_; lean_object* v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; lean_object* v_snd_926_; 
v___x_921_ = lean_box(v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_918_);
v___x_923_ = ((size_t)0ULL);
v___x_924_ = lean_usize_of_nat(v___x_919_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_898_, v___x_823_, v___x_917_, v___x_923_, v___x_924_, v___x_922_);
lean_dec_ref(v___x_917_);
v_snd_926_ = lean_ctor_get(v___x_925_, 1);
lean_inc(v_snd_926_);
lean_dec_ref(v___x_925_);
v___y_825_ = v_snd_926_;
goto v___jp_824_;
}
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_927_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_928_ = l_Lean_Syntax_getArgs(v___x_927_);
lean_dec(v___x_927_);
v___x_929_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31));
v___x_930_ = lean_array_get_size(v___x_928_);
v___x_931_ = lean_nat_dec_lt(v___x_765_, v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_928_);
v___y_773_ = v___x_929_;
goto v___jp_772_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; size_t v___x_934_; size_t v___x_935_; lean_object* v___x_936_; lean_object* v_snd_937_; 
v___x_932_ = lean_box(v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_929_);
v___x_934_ = ((size_t)0ULL);
v___x_935_ = lean_usize_of_nat(v___x_930_);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_823_, v___x_771_, v___x_928_, v___x_934_, v___x_935_, v___x_933_);
lean_dec_ref(v___x_928_);
v_snd_937_ = lean_ctor_get(v___x_936_, 1);
lean_inc(v_snd_937_);
lean_dec_ref(v___x_936_);
v___y_773_ = v_snd_937_;
goto v___jp_772_;
}
}
v___jp_824_:
{
size_t v_sz_826_; size_t v___x_827_; lean_object* v___x_828_; 
v_sz_826_ = lean_array_size(v___y_825_);
v___x_827_ = ((size_t)0ULL);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v_sz_826_, v___x_827_, v___y_825_);
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
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
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
lean_dec_ref_known(v___x_828_, 1);
v_sz_847_ = lean_array_size(v_val_846_);
v_vs_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_847_, v___x_827_, v_val_846_);
v_ks_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v_sz_847_, v___x_827_, v_val_846_);
v_sz_850_ = lean_array_size(v_ks_849_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___redArg(v_sz_850_, v___x_827_, v_ks_849_, v_a_752_);
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
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
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
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v___x_860_, v_quotContext_857_, v_currMacroScope_858_, v_sz_873_, v___x_827_, v___x_872_);
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
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = l_Lean_Syntax_getArg(v___x_758_, v___x_765_);
lean_inc(v___x_938_);
v___x_939_ = l_Lean_Syntax_matchesNull(v___x_938_, v___x_765_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; 
v___x_940_ = l_Lean_Syntax_matchesNull(v___x_938_, v___x_757_);
if (v___x_940_ == 0)
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec(v___x_758_);
v___x_942_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_942_;
}
else
{
lean_object* v_quotContext_943_; lean_object* v_currMacroScope_944_; lean_object* v_ref_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_quotContext_943_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_944_ = lean_ctor_get(v_a_751_, 2);
v_ref_945_ = lean_ctor_get(v_a_751_, 5);
v___x_946_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_947_ = l_Lean_SourceInfo_fromRef(v_ref_945_, v___x_940_);
v___x_948_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_949_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_950_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_944_);
lean_inc(v_quotContext_943_);
v___x_951_ = l_Lean_addMacroScope(v_quotContext_943_, v___x_950_, v_currMacroScope_944_);
v___x_952_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_947_, 2);
v___x_953_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_953_, 0, v___x_947_);
lean_ctor_set(v___x_953_, 1, v___x_949_);
lean_ctor_set(v___x_953_, 2, v___x_951_);
lean_ctor_set(v___x_953_, 3, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_955_ = l_Lean_Syntax_node1(v___x_947_, v___x_954_, v___x_946_);
v___x_956_ = l_Lean_Syntax_node2(v___x_947_, v___x_948_, v___x_953_, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_a_752_);
return v___x_957_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_959_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_958_);
v___x_960_ = l_Lean_Syntax_isOfKind(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
uint8_t v___x_961_; 
lean_dec(v___x_958_);
v___x_961_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v___x_758_);
v___x_962_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_962_;
}
else
{
lean_object* v_quotContext_963_; lean_object* v_currMacroScope_964_; lean_object* v_ref_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_quotContext_963_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_964_ = lean_ctor_get(v_a_751_, 2);
v_ref_965_ = lean_ctor_get(v_a_751_, 5);
v___x_966_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_967_ = l_Lean_SourceInfo_fromRef(v_ref_965_, v___x_939_);
v___x_968_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_969_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_970_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_964_);
lean_inc(v_quotContext_963_);
v___x_971_ = l_Lean_addMacroScope(v_quotContext_963_, v___x_970_, v_currMacroScope_964_);
v___x_972_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_967_, 2);
v___x_973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_973_, 0, v___x_967_);
lean_ctor_set(v___x_973_, 1, v___x_969_);
lean_ctor_set(v___x_973_, 2, v___x_971_);
lean_ctor_set(v___x_973_, 3, v___x_972_);
v___x_974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_975_ = l_Lean_Syntax_node1(v___x_967_, v___x_974_, v___x_966_);
v___x_976_ = l_Lean_Syntax_node2(v___x_967_, v___x_968_, v___x_973_, v___x_975_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v_a_752_);
return v___x_977_;
}
}
else
{
lean_object* v_quotContext_978_; lean_object* v_currMacroScope_979_; lean_object* v_ref_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec(v___x_758_);
v_quotContext_978_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_979_ = lean_ctor_get(v_a_751_, 2);
v_ref_980_ = lean_ctor_get(v_a_751_, 5);
v___x_981_ = l_Lean_SourceInfo_fromRef(v_ref_980_, v___x_939_);
v___x_982_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_983_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_984_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_979_, 2);
lean_inc_n(v_quotContext_978_, 2);
v___x_985_ = l_Lean_addMacroScope(v_quotContext_978_, v___x_984_, v_currMacroScope_979_);
v___x_986_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_981_, 10);
v___x_987_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_987_, 0, v___x_981_);
lean_ctor_set(v___x_987_, 1, v___x_983_);
lean_ctor_set(v___x_987_, 2, v___x_985_);
lean_ctor_set(v___x_987_, 3, v___x_986_);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_989_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_981_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_994_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_995_ = lean_box(0);
v___x_996_ = l_Lean_addMacroScope(v_quotContext_978_, v___x_995_, v_currMacroScope_979_);
v___x_997_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_998_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_998_, 0, v___x_981_);
lean_ctor_set(v___x_998_, 1, v___x_994_);
lean_ctor_set(v___x_998_, 2, v___x_996_);
lean_ctor_set(v___x_998_, 3, v___x_997_);
v___x_999_ = l_Lean_Syntax_node1(v___x_981_, v___x_993_, v___x_998_);
v___x_1000_ = l_Lean_Syntax_node2(v___x_981_, v___x_990_, v___x_992_, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1002_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_981_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node2(v___x_981_, v___x_1001_, v___x_1003_, v___x_958_);
v___x_1005_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_981_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node3(v___x_981_, v___x_989_, v___x_1000_, v___x_1004_, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node1(v___x_981_, v___x_988_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node2(v___x_981_, v___x_982_, v___x_987_, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_a_752_);
return v___x_1010_;
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
lean_dec(v___x_938_);
v___x_1011_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_1012_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_1011_);
v___x_1013_ = l_Lean_Syntax_isOfKind(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
uint8_t v___x_1014_; 
lean_dec(v___x_1011_);
v___x_1014_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec(v___x_758_);
v___x_1015_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1015_;
}
else
{
lean_object* v_quotContext_1016_; lean_object* v_currMacroScope_1017_; lean_object* v_ref_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_quotContext_1016_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1017_ = lean_ctor_get(v_a_751_, 2);
v_ref_1018_ = lean_ctor_get(v_a_751_, 5);
v___x_1019_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1020_ = l_Lean_SourceInfo_fromRef(v_ref_1018_, v___x_769_);
v___x_1021_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1022_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1023_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1017_);
lean_inc(v_quotContext_1016_);
v___x_1024_ = l_Lean_addMacroScope(v_quotContext_1016_, v___x_1023_, v_currMacroScope_1017_);
v___x_1025_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1020_, 2);
v___x_1026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1020_);
lean_ctor_set(v___x_1026_, 1, v___x_1022_);
lean_ctor_set(v___x_1026_, 2, v___x_1024_);
lean_ctor_set(v___x_1026_, 3, v___x_1025_);
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1028_ = l_Lean_Syntax_node1(v___x_1020_, v___x_1027_, v___x_1019_);
v___x_1029_ = l_Lean_Syntax_node2(v___x_1020_, v___x_1021_, v___x_1026_, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_a_752_);
return v___x_1030_;
}
}
else
{
lean_object* v_quotContext_1031_; lean_object* v_currMacroScope_1032_; lean_object* v_ref_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v___x_758_);
v_quotContext_1031_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1032_ = lean_ctor_get(v_a_751_, 2);
v_ref_1033_ = lean_ctor_get(v_a_751_, 5);
v___x_1034_ = l_Lean_SourceInfo_fromRef(v_ref_1033_, v___x_769_);
v___x_1035_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1036_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1037_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1032_);
lean_inc(v_quotContext_1031_);
v___x_1038_ = l_Lean_addMacroScope(v_quotContext_1031_, v___x_1037_, v_currMacroScope_1032_);
v___x_1039_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1034_, 2);
v___x_1040_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1034_);
lean_ctor_set(v___x_1040_, 1, v___x_1036_);
lean_ctor_set(v___x_1040_, 2, v___x_1038_);
lean_ctor_set(v___x_1040_, 3, v___x_1039_);
v___x_1041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1042_ = l_Lean_Syntax_node1(v___x_1034_, v___x_1041_, v___x_1011_);
v___x_1043_ = l_Lean_Syntax_node2(v___x_1034_, v___x_1035_, v___x_1040_, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v_a_752_);
return v___x_1044_;
}
}
}
v___jp_772_:
{
size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; 
v_sz_774_ = lean_array_size(v___y_773_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_774_, v___x_775_, v___y_773_);
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
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
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
lean_dec_ref_known(v___x_776_, 1);
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
v___x_805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_806_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19));
v___x_807_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20));
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_798_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
v_sz_810_ = lean_array_size(v_val_794_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v___x_798_, v_sz_810_, v___x_775_, v_val_794_);
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
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = l_Lean_Syntax_getArg(v___x_758_, v___x_765_);
lean_inc(v___x_1045_);
v___x_1046_ = l_Lean_Syntax_matchesNull(v___x_1045_, v___x_765_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; 
v___x_1047_ = l_Lean_Syntax_matchesNull(v___x_1045_, v___x_757_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec(v___x_758_);
v___x_1049_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1049_;
}
else
{
lean_object* v_quotContext_1050_; lean_object* v_currMacroScope_1051_; lean_object* v_ref_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_quotContext_1050_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1051_ = lean_ctor_get(v_a_751_, 2);
v_ref_1052_ = lean_ctor_get(v_a_751_, 5);
v___x_1053_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1054_ = l_Lean_SourceInfo_fromRef(v_ref_1052_, v___x_1047_);
v___x_1055_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1056_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1057_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1051_);
lean_inc(v_quotContext_1050_);
v___x_1058_ = l_Lean_addMacroScope(v_quotContext_1050_, v___x_1057_, v_currMacroScope_1051_);
v___x_1059_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1054_, 2);
v___x_1060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1054_);
lean_ctor_set(v___x_1060_, 1, v___x_1056_);
lean_ctor_set(v___x_1060_, 2, v___x_1058_);
lean_ctor_set(v___x_1060_, 3, v___x_1059_);
v___x_1061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1062_ = l_Lean_Syntax_node1(v___x_1054_, v___x_1061_, v___x_1053_);
v___x_1063_ = l_Lean_Syntax_node2(v___x_1054_, v___x_1055_, v___x_1060_, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_a_752_);
return v___x_1064_;
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_1066_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1065_);
v___x_1067_ = l_Lean_Syntax_isOfKind(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; 
lean_dec(v___x_1065_);
v___x_1068_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec(v___x_758_);
v___x_1069_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1069_;
}
else
{
lean_object* v_quotContext_1070_; lean_object* v_currMacroScope_1071_; lean_object* v_ref_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_quotContext_1070_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1071_ = lean_ctor_get(v_a_751_, 2);
v_ref_1072_ = lean_ctor_get(v_a_751_, 5);
v___x_1073_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1074_ = l_Lean_SourceInfo_fromRef(v_ref_1072_, v___x_1046_);
v___x_1075_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1076_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1077_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1071_);
lean_inc(v_quotContext_1070_);
v___x_1078_ = l_Lean_addMacroScope(v_quotContext_1070_, v___x_1077_, v_currMacroScope_1071_);
v___x_1079_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1074_, 2);
v___x_1080_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1074_);
lean_ctor_set(v___x_1080_, 1, v___x_1076_);
lean_ctor_set(v___x_1080_, 2, v___x_1078_);
lean_ctor_set(v___x_1080_, 3, v___x_1079_);
v___x_1081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1082_ = l_Lean_Syntax_node1(v___x_1074_, v___x_1081_, v___x_1073_);
v___x_1083_ = l_Lean_Syntax_node2(v___x_1074_, v___x_1075_, v___x_1080_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_752_);
return v___x_1084_;
}
}
else
{
lean_object* v_quotContext_1085_; lean_object* v_currMacroScope_1086_; lean_object* v_ref_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v___x_758_);
v_quotContext_1085_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1086_ = lean_ctor_get(v_a_751_, 2);
v_ref_1087_ = lean_ctor_get(v_a_751_, 5);
v___x_1088_ = l_Lean_SourceInfo_fromRef(v_ref_1087_, v___x_1046_);
v___x_1089_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1090_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1091_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_1086_, 2);
lean_inc_n(v_quotContext_1085_, 2);
v___x_1092_ = l_Lean_addMacroScope(v_quotContext_1085_, v___x_1091_, v_currMacroScope_1086_);
v___x_1093_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1088_, 10);
v___x_1094_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1088_);
lean_ctor_set(v___x_1094_, 1, v___x_1090_);
lean_ctor_set(v___x_1094_, 2, v___x_1092_);
lean_ctor_set(v___x_1094_, 3, v___x_1093_);
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1096_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
v___x_1099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1088_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_1101_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_1102_ = lean_box(0);
v___x_1103_ = l_Lean_addMacroScope(v_quotContext_1085_, v___x_1102_, v_currMacroScope_1086_);
v___x_1104_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_1105_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1088_);
lean_ctor_set(v___x_1105_, 1, v___x_1101_);
lean_ctor_set(v___x_1105_, 2, v___x_1103_);
lean_ctor_set(v___x_1105_, 3, v___x_1104_);
v___x_1106_ = l_Lean_Syntax_node1(v___x_1088_, v___x_1100_, v___x_1105_);
v___x_1107_ = l_Lean_Syntax_node2(v___x_1088_, v___x_1097_, v___x_1099_, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1109_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1088_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Lean_Syntax_node2(v___x_1088_, v___x_1108_, v___x_1110_, v___x_1065_);
v___x_1112_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1088_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = l_Lean_Syntax_node3(v___x_1088_, v___x_1096_, v___x_1107_, v___x_1111_, v___x_1113_);
v___x_1115_ = l_Lean_Syntax_node1(v___x_1088_, v___x_1095_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node2(v___x_1088_, v___x_1089_, v___x_1094_, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_a_752_);
return v___x_1117_;
}
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
lean_dec(v___x_1045_);
v___x_1118_ = l_Lean_Syntax_getArg(v___x_758_, v___x_757_);
v___x_1119_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1118_);
v___x_1120_ = l_Lean_Syntax_isOfKind(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; 
lean_dec(v___x_1118_);
v___x_1121_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec(v___x_758_);
v___x_1122_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1122_;
}
else
{
lean_object* v_quotContext_1123_; lean_object* v_currMacroScope_1124_; lean_object* v_ref_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_quotContext_1123_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1124_ = lean_ctor_get(v_a_751_, 2);
v_ref_1125_ = lean_ctor_get(v_a_751_, 5);
v___x_1126_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1127_ = l_Lean_SourceInfo_fromRef(v_ref_1125_, v___x_767_);
v___x_1128_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1129_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1130_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1124_);
lean_inc(v_quotContext_1123_);
v___x_1131_ = l_Lean_addMacroScope(v_quotContext_1123_, v___x_1130_, v_currMacroScope_1124_);
v___x_1132_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1127_, 2);
v___x_1133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1127_);
lean_ctor_set(v___x_1133_, 1, v___x_1129_);
lean_ctor_set(v___x_1133_, 2, v___x_1131_);
lean_ctor_set(v___x_1133_, 3, v___x_1132_);
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1135_ = l_Lean_Syntax_node1(v___x_1127_, v___x_1134_, v___x_1126_);
v___x_1136_ = l_Lean_Syntax_node2(v___x_1127_, v___x_1128_, v___x_1133_, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_a_752_);
return v___x_1137_;
}
}
else
{
lean_object* v_quotContext_1138_; lean_object* v_currMacroScope_1139_; lean_object* v_ref_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v___x_758_);
v_quotContext_1138_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1139_ = lean_ctor_get(v_a_751_, 2);
v_ref_1140_ = lean_ctor_get(v_a_751_, 5);
v___x_1141_ = l_Lean_SourceInfo_fromRef(v_ref_1140_, v___x_767_);
v___x_1142_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1143_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1144_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1139_);
lean_inc(v_quotContext_1138_);
v___x_1145_ = l_Lean_addMacroScope(v_quotContext_1138_, v___x_1144_, v_currMacroScope_1139_);
v___x_1146_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1141_, 2);
v___x_1147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1141_);
lean_ctor_set(v___x_1147_, 1, v___x_1143_);
lean_ctor_set(v___x_1147_, 2, v___x_1145_);
lean_ctor_set(v___x_1147_, 3, v___x_1146_);
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1149_ = l_Lean_Syntax_node1(v___x_1141_, v___x_1148_, v___x_1118_);
v___x_1150_ = l_Lean_Syntax_node2(v___x_1141_, v___x_1142_, v___x_1147_, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v_a_752_);
return v___x_1151_;
}
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = l_Lean_Syntax_getArg(v___x_758_, v___x_765_);
v___x_1153_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v___x_1152_);
v___x_1154_ = l_Lean_Syntax_isOfKind(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint8_t v___x_1155_; 
lean_dec(v___x_1152_);
v___x_1155_ = l_Lean_Syntax_isAntiquot(v___x_758_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec(v___x_758_);
v___x_1156_ = l_Lean_Macro_throwUnsupported___redArg(v_a_752_);
return v___x_1156_;
}
else
{
lean_object* v_quotContext_1157_; lean_object* v_currMacroScope_1158_; lean_object* v_ref_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_quotContext_1157_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1158_ = lean_ctor_get(v_a_751_, 2);
v_ref_1159_ = lean_ctor_get(v_a_751_, 5);
v___x_1160_ = l_Lean_Syntax_getAntiquotTerm(v___x_758_);
lean_dec(v___x_758_);
v___x_1161_ = l_Lean_SourceInfo_fromRef(v_ref_1159_, v___x_764_);
v___x_1162_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1163_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1164_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1158_);
lean_inc(v_quotContext_1157_);
v___x_1165_ = l_Lean_addMacroScope(v_quotContext_1157_, v___x_1164_, v_currMacroScope_1158_);
v___x_1166_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1161_, 2);
v___x_1167_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1161_);
lean_ctor_set(v___x_1167_, 1, v___x_1163_);
lean_ctor_set(v___x_1167_, 2, v___x_1165_);
lean_ctor_set(v___x_1167_, 3, v___x_1166_);
v___x_1168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1169_ = l_Lean_Syntax_node1(v___x_1161_, v___x_1168_, v___x_1160_);
v___x_1170_ = l_Lean_Syntax_node2(v___x_1161_, v___x_1162_, v___x_1167_, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v_a_752_);
return v___x_1171_;
}
}
else
{
lean_object* v_quotContext_1172_; lean_object* v_currMacroScope_1173_; lean_object* v_ref_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v___x_758_);
v_quotContext_1172_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1173_ = lean_ctor_get(v_a_751_, 2);
v_ref_1174_ = lean_ctor_get(v_a_751_, 5);
v___x_1175_ = l_Lean_SourceInfo_fromRef(v_ref_1174_, v___x_764_);
v___x_1176_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1177_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45);
v___x_1178_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46));
lean_inc(v_currMacroScope_1173_);
lean_inc(v_quotContext_1172_);
v___x_1179_ = l_Lean_addMacroScope(v_quotContext_1172_, v___x_1178_, v_currMacroScope_1173_);
v___x_1180_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50));
lean_inc_n(v___x_1175_, 2);
v___x_1181_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1175_);
lean_ctor_set(v___x_1181_, 1, v___x_1177_);
lean_ctor_set(v___x_1181_, 2, v___x_1179_);
lean_ctor_set(v___x_1181_, 3, v___x_1180_);
v___x_1182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1183_ = l_Lean_Syntax_node1(v___x_1175_, v___x_1182_, v___x_1152_);
v___x_1184_ = l_Lean_Syntax_node2(v___x_1175_, v___x_1176_, v___x_1181_, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v_a_752_);
return v___x_1185_;
}
}
}
else
{
lean_object* v_quotContext_1186_; lean_object* v_currMacroScope_1187_; lean_object* v_ref_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec(v___x_758_);
v_quotContext_1186_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1187_ = lean_ctor_get(v_a_751_, 2);
v_ref_1188_ = lean_ctor_get(v_a_751_, 5);
v___x_1189_ = l_Lean_SourceInfo_fromRef(v_ref_1188_, v___x_762_);
v___x_1190_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1191_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1192_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1187_, 2);
lean_inc_n(v_quotContext_1186_, 2);
v___x_1193_ = l_Lean_addMacroScope(v_quotContext_1186_, v___x_1192_, v_currMacroScope_1187_);
v___x_1194_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1189_, 3);
v___x_1195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v___x_1191_);
lean_ctor_set(v___x_1195_, 2, v___x_1193_);
lean_ctor_set(v___x_1195_, 3, v___x_1194_);
v___x_1196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1197_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60);
v___x_1198_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62));
v___x_1199_ = l_Lean_addMacroScope(v_quotContext_1186_, v___x_1198_, v_currMacroScope_1187_);
v___x_1200_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66));
v___x_1201_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1189_);
lean_ctor_set(v___x_1201_, 1, v___x_1197_);
lean_ctor_set(v___x_1201_, 2, v___x_1199_);
lean_ctor_set(v___x_1201_, 3, v___x_1200_);
v___x_1202_ = l_Lean_Syntax_node1(v___x_1189_, v___x_1196_, v___x_1201_);
v___x_1203_ = l_Lean_Syntax_node2(v___x_1189_, v___x_1190_, v___x_1195_, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v_a_752_);
return v___x_1204_;
}
}
else
{
lean_object* v_quotContext_1205_; lean_object* v_currMacroScope_1206_; lean_object* v_ref_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec(v___x_758_);
v_quotContext_1205_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1206_ = lean_ctor_get(v_a_751_, 2);
v_ref_1207_ = lean_ctor_get(v_a_751_, 5);
v___x_1208_ = l_Lean_SourceInfo_fromRef(v_ref_1207_, v___x_760_);
v___x_1209_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1210_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1211_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1206_, 2);
lean_inc_n(v_quotContext_1205_, 2);
v___x_1212_ = l_Lean_addMacroScope(v_quotContext_1205_, v___x_1211_, v_currMacroScope_1206_);
v___x_1213_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1208_, 3);
v___x_1214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1208_);
lean_ctor_set(v___x_1214_, 1, v___x_1210_);
lean_ctor_set(v___x_1214_, 2, v___x_1212_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
v___x_1215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1216_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68);
v___x_1217_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69));
v___x_1218_ = l_Lean_addMacroScope(v_quotContext_1205_, v___x_1217_, v_currMacroScope_1206_);
v___x_1219_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73));
v___x_1220_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1208_);
lean_ctor_set(v___x_1220_, 1, v___x_1216_);
lean_ctor_set(v___x_1220_, 2, v___x_1218_);
lean_ctor_set(v___x_1220_, 3, v___x_1219_);
v___x_1221_ = l_Lean_Syntax_node1(v___x_1208_, v___x_1215_, v___x_1220_);
v___x_1222_ = l_Lean_Syntax_node2(v___x_1208_, v___x_1209_, v___x_1214_, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v_a_752_);
return v___x_1223_;
}
}
else
{
lean_object* v_quotContext_1224_; lean_object* v_currMacroScope_1225_; lean_object* v_ref_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec(v___x_758_);
v_quotContext_1224_ = lean_ctor_get(v_a_751_, 1);
v_currMacroScope_1225_ = lean_ctor_get(v_a_751_, 2);
v_ref_1226_ = lean_ctor_get(v_a_751_, 5);
v___x_1227_ = 0;
v___x_1228_ = l_Lean_SourceInfo_fromRef(v_ref_1226_, v___x_1227_);
v___x_1229_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75);
v___x_1230_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76));
lean_inc(v_currMacroScope_1225_);
lean_inc(v_quotContext_1224_);
v___x_1231_ = l_Lean_addMacroScope(v_quotContext_1224_, v___x_1230_, v_currMacroScope_1225_);
v___x_1232_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80));
v___x_1233_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1228_);
lean_ctor_set(v___x_1233_, 1, v___x_1229_);
lean_ctor_set(v___x_1233_, 2, v___x_1231_);
lean_ctor_set(v___x_1233_, 3, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_a_752_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___boxed(lean_object* v_x_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(v_x_1235_, v_a_1236_, v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(size_t v_sz_1239_, size_t v_i_1240_, lean_object* v_bs_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___redArg(v_sz_1239_, v_i_1240_, v_bs_1241_, v___y_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(lean_object* v_sz_1245_, lean_object* v_i_1246_, lean_object* v_bs_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
size_t v_sz_boxed_1250_; size_t v_i_boxed_1251_; lean_object* v_res_1252_; 
v_sz_boxed_1250_ = lean_unbox_usize(v_sz_1245_);
lean_dec(v_sz_1245_);
v_i_boxed_1251_ = lean_unbox_usize(v_i_1246_);
lean_dec(v_i_1246_);
v_res_1252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v_sz_boxed_1250_, v_i_boxed_1251_, v_bs_1247_, v___y_1248_, v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1252_;
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
