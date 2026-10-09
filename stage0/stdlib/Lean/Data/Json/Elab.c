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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(uint8_t v___x_275_, size_t v_sz_276_, size_t v_i_277_, lean_object* v_bs_278_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_275_ = stack[0].m_num;
size_t v_sz_276_ = stack[1].m_num;
size_t v_i_277_ = stack[2].m_num;
lean_object* v_bs_278_ = stack[3].m_obj;
lean_object* v_res_299_;
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v___x_275_, v_sz_276_, v_i_277_, v_bs_278_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(lean_object* v___x_300_, lean_object* v_sz_301_, lean_object* v_i_302_, lean_object* v_bs_303_){
_start:
{
uint8_t v___x_32528__boxed_304_; size_t v_sz_boxed_305_; size_t v_i_boxed_306_; lean_object* v_res_307_; 
v___x_32528__boxed_304_ = lean_unbox(v___x_300_);
v_sz_boxed_305_ = lean_unbox_usize(v_sz_301_);
lean_dec(v_sz_301_);
v_i_boxed_306_ = lean_unbox_usize(v_i_302_);
lean_dec(v_i_302_);
v_res_307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v___x_32528__boxed_304_, v_sz_boxed_305_, v_i_boxed_306_, v_bs_303_);
return v_res_307_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(size_t v_sz_308_, size_t v_i_309_, lean_object* v_bs_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_lt(v_i_309_, v_sz_308_);
if (v___x_311_ == 0)
{
return v_bs_310_;
}
else
{
lean_object* v_v_312_; lean_object* v_fst_313_; lean_object* v___x_314_; lean_object* v_bs_x27_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v_v_312_ = lean_array_uget_borrowed(v_bs_310_, v_i_309_);
v_fst_313_ = lean_ctor_get(v_v_312_, 0);
lean_inc(v_fst_313_);
v___x_314_ = lean_unsigned_to_nat(0u);
v_bs_x27_315_ = lean_array_uset(v_bs_310_, v_i_309_, v___x_314_);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_309_, v___x_316_);
v___x_318_ = lean_array_uset(v_bs_x27_315_, v_i_309_, v_fst_313_);
v_i_309_ = v___x_317_;
v_bs_310_ = v___x_318_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_308_ = stack[0].m_num;
size_t v_i_309_ = stack[1].m_num;
lean_object* v_bs_310_ = stack[2].m_obj;
lean_object* v_res_320_;
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v_sz_308_, v_i_309_, v_bs_310_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(lean_object* v_sz_321_, lean_object* v_i_322_, lean_object* v_bs_323_){
_start:
{
size_t v_sz_boxed_324_; size_t v_i_boxed_325_; lean_object* v_res_326_; 
v_sz_boxed_324_ = lean_unbox_usize(v_sz_321_);
lean_dec(v_sz_321_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v_sz_boxed_324_, v_i_boxed_325_, v_bs_323_);
return v_res_326_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(size_t v_sz_327_, size_t v_i_328_, lean_object* v_bs_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_328_, v_sz_327_);
if (v___x_330_ == 0)
{
return v_bs_329_;
}
else
{
lean_object* v_v_331_; lean_object* v_snd_332_; lean_object* v___x_333_; lean_object* v_bs_x27_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v_v_331_ = lean_array_uget_borrowed(v_bs_329_, v_i_328_);
v_snd_332_ = lean_ctor_get(v_v_331_, 1);
lean_inc(v_snd_332_);
v___x_333_ = lean_unsigned_to_nat(0u);
v_bs_x27_334_ = lean_array_uset(v_bs_329_, v_i_328_, v___x_333_);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_328_, v___x_335_);
v___x_337_ = lean_array_uset(v_bs_x27_334_, v_i_328_, v_snd_332_);
v_i_328_ = v___x_336_;
v_bs_329_ = v___x_337_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_327_ = stack[0].m_num;
size_t v_i_328_ = stack[1].m_num;
lean_object* v_bs_329_ = stack[2].m_obj;
lean_object* v_res_339_;
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_327_, v_i_328_, v_bs_329_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(lean_object* v_sz_340_, lean_object* v_i_341_, lean_object* v_bs_342_){
_start:
{
size_t v_sz_boxed_343_; size_t v_i_boxed_344_; lean_object* v_res_345_; 
v_sz_boxed_343_ = lean_unbox_usize(v_sz_340_);
lean_dec(v_sz_340_);
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_boxed_343_, v_i_boxed_344_, v_bs_342_);
return v_res_345_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(uint8_t v___x_346_, size_t v_sz_347_, size_t v_i_348_, lean_object* v_bs_349_, lean_object* v___y_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_lt(v_i_348_, v_sz_347_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_bs_349_);
lean_ctor_set(v___x_352_, 1, v___y_350_);
return v___x_352_;
}
else
{
lean_object* v_v_353_; lean_object* v___x_354_; lean_object* v_bs_x27_355_; lean_object* v_a_357_; lean_object* v_a_358_; lean_object* v___y_364_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_v_353_ = lean_array_uget(v_bs_349_, v_i_348_);
v___x_354_ = lean_unsigned_to_nat(0u);
v_bs_x27_355_ = lean_array_uset(v_bs_349_, v_i_348_, v___x_354_);
v___x_376_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_v_353_);
v___x_377_ = l_Lean_Syntax_isOfKind(v_v_353_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_v_353_);
v___x_378_ = l_Lean_Macro_throwUnsupported___redArg(v___y_350_);
v___y_364_ = v___x_378_;
goto v___jp_363_;
}
else
{
lean_object* v_k_379_; 
v_k_379_ = l_Lean_Syntax_getArg(v_v_353_, v___x_354_);
lean_dec(v_v_353_);
if (v___x_346_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__5));
lean_inc(v_k_379_);
v___x_386_ = l_Lean_Syntax_isOfKind(v_k_379_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v_k_379_);
v___x_388_ = l_Lean_Syntax_isOfKind(v_k_379_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec(v_k_379_);
v___x_389_ = l_Lean_Macro_throwUnsupported___redArg(v___y_350_);
v___y_364_ = v___x_389_;
goto v___jp_363_;
}
else
{
v_a_357_ = v_k_379_;
v_a_358_ = v___y_350_;
goto v___jp_356_;
}
}
else
{
goto v___jp_380_;
}
}
else
{
goto v___jp_380_;
}
v___jp_380_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_381_ = l_Lean_TSyntax_getId(v_k_379_);
lean_dec(v_k_379_);
v___x_382_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_381_, v___x_377_);
v___x_383_ = lean_box(2);
v___x_384_ = l_Lean_Syntax_mkStrLit(v___x_382_, v___x_383_);
v_a_357_ = v___x_384_;
v_a_358_ = v___y_350_;
goto v___jp_356_;
}
}
v___jp_356_:
{
size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_add(v_i_348_, v___x_359_);
v___x_361_ = lean_array_uset(v_bs_x27_355_, v_i_348_, v_a_357_);
v_i_348_ = v___x_360_;
v_bs_349_ = v___x_361_;
v___y_350_ = v_a_358_;
goto _start;
}
v___jp_363_:
{
if (lean_obj_tag(v___y_364_) == 0)
{
lean_object* v_a_365_; lean_object* v_a_366_; 
v_a_365_ = lean_ctor_get(v___y_364_, 0);
lean_inc(v_a_365_);
v_a_366_ = lean_ctor_get(v___y_364_, 1);
lean_inc(v_a_366_);
lean_dec_ref_known(v___y_364_, 2);
v_a_357_ = v_a_365_;
v_a_358_ = v_a_366_;
goto v___jp_356_;
}
else
{
lean_object* v_a_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_bs_x27_355_);
v_a_367_ = lean_ctor_get(v___y_364_, 0);
v_a_368_ = lean_ctor_get(v___y_364_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v___y_364_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___y_364_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_inc(v_a_367_);
lean_dec(v___y_364_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_367_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_346_ = stack[0].m_num;
size_t v_sz_347_ = stack[1].m_num;
size_t v_i_348_ = stack[2].m_num;
lean_object* v_bs_349_ = stack[3].m_obj;
lean_object* v___y_350_ = stack[4].m_obj;
lean_object* v_res_390_;
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(v___x_346_, v_sz_347_, v_i_348_, v_bs_349_, v___y_350_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg___boxed(lean_object* v___x_391_, lean_object* v_sz_392_, lean_object* v_i_393_, lean_object* v_bs_394_, lean_object* v___y_395_){
_start:
{
uint8_t v___x_32642__boxed_396_; size_t v_sz_boxed_397_; size_t v_i_boxed_398_; lean_object* v_res_399_; 
v___x_32642__boxed_396_ = lean_unbox(v___x_391_);
v_sz_boxed_397_ = lean_unbox_usize(v_sz_392_);
lean_dec(v_sz_392_);
v_i_boxed_398_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(v___x_32642__boxed_396_, v_sz_boxed_397_, v_i_boxed_398_, v_bs_394_, v___y_395_);
return v_res_399_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(uint8_t v___x_400_, size_t v_sz_401_, size_t v_i_402_, lean_object* v_bs_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = lean_usize_dec_lt(v_i_402_, v_sz_401_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_bs_403_);
lean_ctor_set(v___x_407_, 1, v___y_405_);
return v___x_407_;
}
else
{
lean_object* v_v_408_; lean_object* v___x_409_; lean_object* v_bs_x27_410_; lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v___y_419_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_v_408_ = lean_array_uget(v_bs_403_, v_i_402_);
v___x_409_ = lean_unsigned_to_nat(0u);
v_bs_x27_410_ = lean_array_uset(v_bs_403_, v_i_402_, v___x_409_);
v___x_431_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__1));
lean_inc(v_v_408_);
v___x_432_ = l_Lean_Syntax_isOfKind(v_v_408_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec(v_v_408_);
v___x_433_ = l_Lean_Macro_throwUnsupported___redArg(v___y_405_);
v___y_419_ = v___x_433_;
goto v___jp_418_;
}
else
{
lean_object* v_k_434_; 
v_k_434_ = l_Lean_Syntax_getArg(v_v_408_, v___x_409_);
lean_dec(v_v_408_);
if (v___x_400_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Json_jsonIdent___closed__5));
lean_inc(v_k_434_);
v___x_441_ = l_Lean_Syntax_isOfKind(v_k_434_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v_k_434_);
v___x_443_ = l_Lean_Syntax_isOfKind(v_k_434_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec(v_k_434_);
v___x_444_ = l_Lean_Macro_throwUnsupported___redArg(v___y_405_);
v___y_419_ = v___x_444_;
goto v___jp_418_;
}
else
{
v_a_412_ = v_k_434_;
v_a_413_ = v___y_405_;
goto v___jp_411_;
}
}
else
{
goto v___jp_435_;
}
}
else
{
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = l_Lean_TSyntax_getId(v_k_434_);
lean_dec(v_k_434_);
v___x_437_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_436_, v___x_432_);
v___x_438_ = lean_box(2);
v___x_439_ = l_Lean_Syntax_mkStrLit(v___x_437_, v___x_438_);
v_a_412_ = v___x_439_;
v_a_413_ = v___y_405_;
goto v___jp_411_;
}
}
v___jp_411_:
{
size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_402_, v___x_414_);
v___x_416_ = lean_array_uset(v_bs_x27_410_, v_i_402_, v_a_412_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(v___x_400_, v_sz_401_, v___x_415_, v___x_416_, v_a_413_);
return v___x_417_;
}
v___jp_418_:
{
if (lean_obj_tag(v___y_419_) == 0)
{
lean_object* v_a_420_; lean_object* v_a_421_; 
v_a_420_ = lean_ctor_get(v___y_419_, 0);
lean_inc(v_a_420_);
v_a_421_ = lean_ctor_get(v___y_419_, 1);
lean_inc(v_a_421_);
lean_dec_ref_known(v___y_419_, 2);
v_a_412_ = v_a_420_;
v_a_413_ = v_a_421_;
goto v___jp_411_;
}
else
{
lean_object* v_a_422_; lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_bs_x27_410_);
v_a_422_ = lean_ctor_get(v___y_419_, 0);
v_a_423_ = lean_ctor_get(v___y_419_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v___y_419_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___y_419_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_inc(v_a_422_);
lean_dec(v___y_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_422_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_400_ = stack[0].m_num;
size_t v_sz_401_ = stack[1].m_num;
size_t v_i_402_ = stack[2].m_num;
lean_object* v_bs_403_ = stack[3].m_obj;
lean_object* v___y_404_ = stack[4].m_obj;
lean_object* v___y_405_ = stack[5].m_obj;
lean_object* v_res_445_;
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_400_, v_sz_401_, v_i_402_, v_bs_403_, v___y_404_, v___y_405_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(lean_object* v___x_446_, lean_object* v_sz_447_, lean_object* v_i_448_, lean_object* v_bs_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_32778__boxed_452_; size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v___x_32778__boxed_452_ = lean_unbox(v___x_446_);
v_sz_boxed_453_ = lean_unbox_usize(v_sz_447_);
lean_dec(v_sz_447_);
v_i_boxed_454_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_32778__boxed_452_, v_sz_boxed_453_, v_i_boxed_454_, v_bs_449_, v___y_450_, v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_455_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__8));
v___x_476_ = l_String_toRawSubstring_x27(v___x_475_);
return v___x_476_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v___x_488_, size_t v_sz_489_, size_t v_i_490_, lean_object* v_bs_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
if (v___x_492_ == 0)
{
lean_dec(v___x_488_);
lean_dec(v___x_487_);
lean_dec(v___x_486_);
return v_bs_491_;
}
else
{
lean_object* v_v_493_; lean_object* v_fst_494_; lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_531_; 
v_v_493_ = lean_array_uget(v_bs_491_, v_i_490_);
v_fst_494_ = lean_ctor_get(v_v_493_, 0);
v_snd_495_ = lean_ctor_get(v_v_493_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_v_493_);
if (v_isSharedCheck_531_ == 0)
{
v___x_497_ = v_v_493_;
v_isShared_498_ = v_isSharedCheck_531_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_inc(v_fst_494_);
lean_dec(v_v_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_531_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_bs_x27_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_499_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_501_ = lean_unsigned_to_nat(0u);
v_bs_x27_502_ = lean_array_uset(v_bs_491_, v_i_490_, v___x_501_);
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__2));
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
lean_inc(v___x_486_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 2);
lean_ctor_set(v___x_497_, 1, v___x_505_);
lean_ctor_set(v___x_497_, 0, v___x_486_);
v___x_507_ = v___x_497_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_530_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_509_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_510_ = lean_box(0);
lean_inc(v___x_488_);
lean_inc(v___x_487_);
v___x_511_ = l_Lean_addMacroScope(v___x_487_, v___x_510_, v___x_488_);
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__12));
lean_inc_n(v___x_486_, 10);
v___x_513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_513_, 0, v___x_486_);
lean_ctor_set(v___x_513_, 1, v___x_509_);
lean_ctor_set(v___x_513_, 2, v___x_511_);
lean_ctor_set(v___x_513_, 3, v___x_512_);
v___x_514_ = l_Lean_Syntax_node1(v___x_486_, v___x_508_, v___x_513_);
v___x_515_ = l_Lean_Syntax_node2(v___x_486_, v___x_504_, v___x_507_, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__4));
v___x_517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_486_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13));
v___x_519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_486_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_Syntax_node2(v___x_486_, v___x_499_, v___x_519_, v_snd_495_);
v___x_521_ = l_Lean_Syntax_node1(v___x_486_, v___x_500_, v___x_520_);
v___x_522_ = l_Lean_Syntax_node3(v___x_486_, v___x_500_, v_fst_494_, v___x_517_, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_486_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Lean_Syntax_node3(v___x_486_, v___x_503_, v___x_515_, v___x_522_, v___x_524_);
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_add(v_i_490_, v___x_526_);
v___x_528_ = lean_array_uset(v_bs_x27_502_, v_i_490_, v___x_525_);
v_i_490_ = v___x_527_;
v_bs_491_ = v___x_528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_486_ = stack[0].m_obj;
lean_object* v___x_487_ = stack[1].m_obj;
lean_object* v___x_488_ = stack[2].m_obj;
size_t v_sz_489_ = stack[3].m_num;
size_t v_i_490_ = stack[4].m_num;
lean_object* v_bs_491_ = stack[5].m_obj;
lean_object* v_res_532_;
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v___x_486_, v___x_487_, v___x_488_, v_sz_489_, v_i_490_, v_bs_491_);
stack->m_obj
 = v_res_532_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___boxed(lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v___x_533_, v___x_534_, v___x_535_, v_sz_boxed_539_, v_i_boxed_540_, v_bs_538_);
return v_res_541_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(size_t v_sz_542_, size_t v_i_543_, lean_object* v_bs_544_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_lt(v_i_543_, v_sz_542_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_bs_544_);
return v___x_546_;
}
else
{
lean_object* v_v_547_; lean_object* v___x_548_; lean_object* v_bs_x27_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v_v_547_ = lean_array_uget(v_bs_544_, v_i_543_);
v___x_548_ = lean_unsigned_to_nat(0u);
v_bs_x27_549_ = lean_array_uset(v_bs_544_, v_i_543_, v___x_548_);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_543_, v___x_550_);
v___x_552_ = lean_array_uset(v_bs_x27_549_, v_i_543_, v_v_547_);
v_i_543_ = v___x_551_;
v_bs_544_ = v___x_552_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_542_ = stack[0].m_num;
size_t v_i_543_ = stack[1].m_num;
lean_object* v_bs_544_ = stack[2].m_obj;
lean_object* v_res_554_;
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_542_, v_i_543_, v_bs_544_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0___boxed(lean_object* v_sz_555_, lean_object* v_i_556_, lean_object* v_bs_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_555_);
lean_dec(v_sz_555_);
v_i_boxed_559_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_boxed_558_, v_i_boxed_559_, v_bs_557_);
return v_res_560_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(lean_object* v___x_561_, size_t v_sz_562_, size_t v_i_563_, lean_object* v_bs_564_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = lean_usize_dec_lt(v_i_563_, v_sz_562_);
if (v___x_565_ == 0)
{
lean_dec(v___x_561_);
return v_bs_564_;
}
else
{
lean_object* v___x_566_; lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_bs_x27_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v___x_566_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
v_v_567_ = lean_array_uget(v_bs_564_, v_i_563_);
v___x_568_ = lean_unsigned_to_nat(0u);
v_bs_x27_569_ = lean_array_uset(v_bs_564_, v_i_563_, v___x_568_);
v___x_570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__13));
lean_inc_n(v___x_561_, 2);
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_561_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_Syntax_node2(v___x_561_, v___x_566_, v___x_571_, v_v_567_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_563_, v___x_573_);
v___x_575_ = lean_array_uset(v_bs_x27_569_, v_i_563_, v___x_572_);
v_i_563_ = v___x_574_;
v_bs_564_ = v___x_575_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_561_ = stack[0].m_obj;
size_t v_sz_562_ = stack[1].m_num;
size_t v_i_563_ = stack[2].m_num;
lean_object* v_bs_564_ = stack[3].m_obj;
lean_object* v_res_577_;
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v___x_561_, v_sz_562_, v_i_563_, v_bs_564_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1___boxed(lean_object* v___x_578_, lean_object* v_sz_579_, lean_object* v_i_580_, lean_object* v_bs_581_){
_start:
{
size_t v_sz_boxed_582_; size_t v_i_boxed_583_; lean_object* v_res_584_; 
v_sz_boxed_582_ = lean_unbox_usize(v_sz_579_);
lean_dec(v_sz_579_);
v_i_boxed_583_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v___x_578_, v_sz_boxed_582_, v_i_boxed_583_, v_bs_581_);
return v_res_584_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(uint8_t v___x_585_, uint8_t v___x_586_, lean_object* v_as_587_, size_t v_i_588_, size_t v_stop_589_, lean_object* v_b_590_){
_start:
{
lean_object* v___y_592_; uint8_t v___x_596_; 
v___x_596_ = lean_usize_dec_eq(v_i_588_, v_stop_589_);
if (v___x_596_ == 0)
{
lean_object* v_fst_597_; uint8_t v___x_598_; 
v_fst_597_ = lean_ctor_get(v_b_590_, 0);
v___x_598_ = lean_unbox(v_fst_597_);
if (v___x_598_ == 0)
{
lean_object* v_snd_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v_snd_599_ = lean_ctor_get(v_b_590_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_b_590_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_b_590_, 0);
lean_dec(v_unused_608_);
v___x_601_ = v_b_590_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snd_599_);
lean_dec(v_b_590_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_box(v___x_585_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_snd_599_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v___y_592_ = v___x_605_;
goto v___jp_591_;
}
}
}
else
{
lean_object* v_snd_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_619_; 
v_snd_609_ = lean_ctor_get(v_b_590_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_b_590_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_b_590_, 0);
lean_dec(v_unused_620_);
v___x_611_ = v_b_590_;
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snd_609_);
lean_dec(v_b_590_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_613_ = lean_array_uget_borrowed(v_as_587_, v_i_588_);
lean_inc(v___x_613_);
v___x_614_ = lean_array_push(v_snd_609_, v___x_613_);
v___x_615_ = lean_box(v___x_586_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___x_614_);
lean_ctor_set(v___x_611_, 0, v___x_615_);
v___x_617_ = v___x_611_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_614_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v___y_592_ = v___x_617_;
goto v___jp_591_;
}
}
}
}
else
{
return v_b_590_;
}
v___jp_591_:
{
size_t v___x_593_; size_t v___x_594_; 
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_i_588_, v___x_593_);
v_i_588_ = v___x_594_;
v_b_590_ = v___y_592_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_585_ = stack[0].m_num;
uint8_t v___x_586_ = stack[1].m_num;
lean_object* v_as_587_ = stack[2].m_obj;
size_t v_i_588_ = stack[3].m_num;
size_t v_stop_589_ = stack[4].m_num;
lean_object* v_b_590_ = stack[5].m_obj;
lean_object* v_res_621_;
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_585_, v___x_586_, v_as_587_, v_i_588_, v_stop_589_, v_b_590_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7___boxed(lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v_as_624_, lean_object* v_i_625_, lean_object* v_stop_626_, lean_object* v_b_627_){
_start:
{
uint8_t v___x_33234__boxed_628_; uint8_t v___x_33235__boxed_629_; size_t v_i_boxed_630_; size_t v_stop_boxed_631_; lean_object* v_res_632_; 
v___x_33234__boxed_628_ = lean_unbox(v___x_622_);
v___x_33235__boxed_629_ = lean_unbox(v___x_623_);
v_i_boxed_630_ = lean_unbox_usize(v_i_625_);
lean_dec(v_i_625_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_626_);
lean_dec(v_stop_626_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_33234__boxed_628_, v___x_33235__boxed_629_, v_as_624_, v_i_boxed_630_, v_stop_boxed_631_, v_b_627_);
lean_dec_ref(v_as_624_);
return v_res_632_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2));
v___x_641_ = l_String_toRawSubstring_x27(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10));
v___x_659_ = l_String_toRawSubstring_x27(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21(void){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Array_mkArray0___redArg();
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__4));
v___x_682_ = l_Lean_mkAtom(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23));
v___x_685_ = l_String_toRawSubstring_x27(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32));
v___x_704_ = l_String_toRawSubstring_x27(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44));
v___x_734_ = l_String_toRawSubstring_x27(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51));
v___x_752_ = l_String_toRawSubstring_x27(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59));
v___x_771_ = l_String_toRawSubstring_x27(v___x_770_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67));
v___x_789_ = l_String_toRawSubstring_x27(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74));
v___x_806_ = l_String_toRawSubstring_x27(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(lean_object* v_x_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Json_termJson_x25___00__closed__1));
lean_inc(v_x_822_);
v___x_826_ = l_Lean_Syntax_isOfKind(v_x_822_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v_x_822_);
v___x_827_ = lean_box(1);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_a_824_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = l_Lean_Syntax_getArg(v_x_822_, v___x_829_);
lean_dec(v_x_822_);
v___x_831_ = ((lean_object*)(l_Lean_Json_jsonNull___closed__2));
lean_inc(v___x_830_);
v___x_832_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_Json_jsonTrue___closed__1));
lean_inc(v___x_830_);
v___x_834_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_Json_jsonFalse___closed__1));
lean_inc(v___x_830_);
v___x_836_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = ((lean_object*)(l_Lean_Json_json___00__closed__1));
lean_inc(v___x_830_);
v___x_839_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__1));
lean_inc(v___x_830_);
v___x_841_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___y_845_; 
v___x_842_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__1));
lean_inc(v___x_830_);
v___x_843_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___y_897_; 
v___x_894_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__1));
lean_inc(v___x_830_);
v___x_895_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_Json_json_x7b___x7d___closed__1));
lean_inc(v___x_830_);
v___x_970_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_969_);
if (v___x_970_ == 0)
{
uint8_t v___x_971_; 
v___x_971_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; 
lean_dec(v___x_830_);
v___x_972_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_972_;
}
else
{
lean_object* v_quotContext_973_; lean_object* v_currMacroScope_974_; lean_object* v_ref_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_quotContext_973_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_974_ = lean_ctor_get(v_a_823_, 2);
v_ref_975_ = lean_ctor_get(v_a_823_, 5);
v___x_976_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
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
v___x_984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_985_ = l_Lean_Syntax_node1(v___x_977_, v___x_984_, v___x_976_);
v___x_986_ = l_Lean_Syntax_node2(v___x_977_, v___x_978_, v___x_983_, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_a_824_);
return v___x_987_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_988_ = l_Lean_Syntax_getArg(v___x_830_, v___x_829_);
v___x_989_ = l_Lean_Syntax_getArgs(v___x_988_);
lean_dec(v___x_988_);
v___x_990_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31));
v___x_991_ = lean_array_get_size(v___x_989_);
v___x_992_ = lean_nat_dec_lt(v___x_837_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___x_989_);
v___y_897_ = v___x_990_;
goto v___jp_896_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; lean_object* v_snd_998_; 
v___x_993_ = lean_box(v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_990_);
v___x_995_ = ((size_t)0ULL);
v___x_996_ = lean_usize_of_nat(v___x_991_);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_970_, v___x_895_, v___x_989_, v___x_995_, v___x_996_, v___x_994_);
lean_dec_ref(v___x_989_);
v_snd_998_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_snd_998_);
lean_dec_ref(v___x_997_);
v___y_897_ = v_snd_998_;
goto v___jp_896_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_999_ = l_Lean_Syntax_getArg(v___x_830_, v___x_829_);
v___x_1000_ = l_Lean_Syntax_getArgs(v___x_999_);
lean_dec(v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31));
v___x_1002_ = lean_array_get_size(v___x_1000_);
v___x_1003_ = lean_nat_dec_lt(v___x_837_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_dec_ref(v___x_1000_);
v___y_845_ = v___x_1001_;
goto v___jp_844_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; lean_object* v_snd_1009_; 
v___x_1004_ = lean_box(v___x_1003_);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1001_);
v___x_1006_ = ((size_t)0ULL);
v___x_1007_ = lean_usize_of_nat(v___x_1002_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_895_, v___x_843_, v___x_1000_, v___x_1006_, v___x_1007_, v___x_1005_);
lean_dec_ref(v___x_1000_);
v_snd_1009_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_snd_1009_);
lean_dec_ref(v___x_1008_);
v___y_845_ = v_snd_1009_;
goto v___jp_844_;
}
}
v___jp_896_:
{
size_t v_sz_898_; size_t v___x_899_; lean_object* v___x_900_; 
v_sz_898_ = lean_array_size(v___y_897_);
v___x_899_ = ((size_t)0ULL);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v___x_895_, v_sz_898_, v___x_899_, v___y_897_);
if (lean_obj_tag(v___x_900_) == 0)
{
uint8_t v___x_901_; 
v___x_901_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v___x_830_);
v___x_902_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_902_;
}
else
{
lean_object* v_quotContext_903_; lean_object* v_currMacroScope_904_; lean_object* v_ref_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_quotContext_903_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_904_ = lean_ctor_get(v_a_823_, 2);
v_ref_905_ = lean_ctor_get(v_a_823_, 5);
v___x_906_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_907_ = l_Lean_SourceInfo_fromRef(v_ref_905_, v___x_895_);
v___x_908_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_909_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_910_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_904_);
lean_inc(v_quotContext_903_);
v___x_911_ = l_Lean_addMacroScope(v_quotContext_903_, v___x_910_, v_currMacroScope_904_);
v___x_912_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_907_, 2);
v___x_913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_913_, 0, v___x_907_);
lean_ctor_set(v___x_913_, 1, v___x_909_);
lean_ctor_set(v___x_913_, 2, v___x_911_);
lean_ctor_set(v___x_913_, 3, v___x_912_);
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_915_ = l_Lean_Syntax_node1(v___x_907_, v___x_914_, v___x_906_);
v___x_916_ = l_Lean_Syntax_node2(v___x_907_, v___x_908_, v___x_913_, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_a_824_);
return v___x_917_;
}
}
else
{
lean_object* v_val_918_; size_t v_sz_919_; lean_object* v_vs_920_; lean_object* v_ks_921_; size_t v_sz_922_; lean_object* v___x_923_; 
lean_dec(v___x_830_);
v_val_918_ = lean_ctor_get(v___x_900_, 0);
lean_inc_n(v_val_918_, 2);
lean_dec_ref_known(v___x_900_, 1);
v_sz_919_ = lean_array_size(v_val_918_);
v_vs_920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_919_, v___x_899_, v_val_918_);
v_ks_921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v_sz_919_, v___x_899_, v_val_918_);
v_sz_922_ = lean_array_size(v_ks_921_);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_895_, v_sz_922_, v___x_899_, v_ks_921_, v_a_823_, v_a_824_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_959_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_a_925_ = lean_ctor_get(v___x_923_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_959_ == 0)
{
v___x_927_ = v___x_923_;
v_isShared_928_ = v_isSharedCheck_959_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_959_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_quotContext_929_; lean_object* v_currMacroScope_930_; lean_object* v_ref_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; size_t v_sz_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v_quotContext_929_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_930_ = lean_ctor_get(v_a_823_, 2);
v_ref_931_ = lean_ctor_get(v_a_823_, 5);
v___x_932_ = l_Lean_SourceInfo_fromRef(v_ref_931_, v___x_895_);
v___x_933_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_934_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24);
v___x_935_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26));
lean_inc_n(v_currMacroScope_930_, 2);
lean_inc_n(v_quotContext_929_, 2);
v___x_936_ = l_Lean_addMacroScope(v_quotContext_929_, v___x_935_, v_currMacroScope_930_);
v___x_937_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28));
lean_inc_n(v___x_932_, 7);
v___x_938_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_938_, 0, v___x_932_);
lean_ctor_set(v___x_938_, 1, v___x_934_);
lean_ctor_set(v___x_938_, 2, v___x_936_);
lean_ctor_set(v___x_938_, 3, v___x_937_);
v___x_939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_940_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30));
v___x_941_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__2));
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_932_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
v___x_944_ = l_Array_zip___redArg(v_a_924_, v_vs_920_);
lean_dec_ref(v_vs_920_);
lean_dec(v_a_924_);
v_sz_945_ = lean_array_size(v___x_944_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v___x_932_, v_quotContext_929_, v_currMacroScope_930_, v_sz_945_, v___x_899_, v___x_944_);
v___x_947_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
v___x_948_ = l_Lean_mkSepArray(v___x_946_, v___x_947_);
lean_dec_ref(v___x_946_);
v___x_949_ = l_Array_append___redArg(v___x_943_, v___x_948_);
lean_dec_ref(v___x_948_);
v___x_950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_950_, 0, v___x_932_);
lean_ctor_set(v___x_950_, 1, v___x_939_);
lean_ctor_set(v___x_950_, 2, v___x_949_);
v___x_951_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__9));
v___x_952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_932_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_Syntax_node3(v___x_932_, v___x_940_, v___x_942_, v___x_950_, v___x_952_);
v___x_954_ = l_Lean_Syntax_node1(v___x_932_, v___x_939_, v___x_953_);
v___x_955_ = l_Lean_Syntax_node2(v___x_932_, v___x_933_, v___x_938_, v___x_954_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_955_);
v___x_957_ = v___x_927_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_a_925_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
else
{
lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v_vs_920_);
v_a_960_ = lean_ctor_get(v___x_923_, 0);
v_a_961_ = lean_ctor_get(v___x_923_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_923_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_inc(v_a_960_);
lean_dec(v___x_923_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_960_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
else
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = l_Lean_Syntax_getArg(v___x_830_, v___x_837_);
lean_inc(v___x_1010_);
v___x_1011_ = l_Lean_Syntax_matchesNull(v___x_1010_, v___x_837_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_Syntax_matchesNull(v___x_1010_, v___x_829_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec(v___x_830_);
v___x_1014_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_1014_;
}
else
{
lean_object* v_quotContext_1015_; lean_object* v_currMacroScope_1016_; lean_object* v_ref_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_quotContext_1015_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1016_ = lean_ctor_get(v_a_823_, 2);
v_ref_1017_ = lean_ctor_get(v_a_823_, 5);
v___x_1018_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_1019_ = l_Lean_SourceInfo_fromRef(v_ref_1017_, v___x_1012_);
v___x_1020_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1021_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1022_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1016_);
lean_inc(v_quotContext_1015_);
v___x_1023_ = l_Lean_addMacroScope(v_quotContext_1015_, v___x_1022_, v_currMacroScope_1016_);
v___x_1024_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1019_, 2);
v___x_1025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1019_);
lean_ctor_set(v___x_1025_, 1, v___x_1021_);
lean_ctor_set(v___x_1025_, 2, v___x_1023_);
lean_ctor_set(v___x_1025_, 3, v___x_1024_);
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1027_ = l_Lean_Syntax_node1(v___x_1019_, v___x_1026_, v___x_1018_);
v___x_1028_ = l_Lean_Syntax_node2(v___x_1019_, v___x_1020_, v___x_1025_, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v_a_824_);
return v___x_1029_;
}
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Syntax_getArg(v___x_830_, v___x_829_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_1030_);
v___x_1066_ = l_Lean_Syntax_isOfKind(v___x_1030_, v___x_1065_);
if (v___x_1066_ == 0)
{
uint8_t v___x_1067_; 
lean_dec(v___x_1030_);
v___x_1067_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_dec(v___x_830_);
v___x_1068_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_1068_;
}
else
{
lean_object* v_quotContext_1069_; lean_object* v_currMacroScope_1070_; lean_object* v_ref_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_quotContext_1069_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1070_ = lean_ctor_get(v_a_823_, 2);
v_ref_1071_ = lean_ctor_get(v_a_823_, 5);
v___x_1072_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_1073_ = l_Lean_SourceInfo_fromRef(v_ref_1071_, v___x_1011_);
v___x_1074_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1075_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1076_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1070_);
lean_inc(v_quotContext_1069_);
v___x_1077_ = l_Lean_addMacroScope(v_quotContext_1069_, v___x_1076_, v_currMacroScope_1070_);
v___x_1078_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1073_, 2);
v___x_1079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1073_);
lean_ctor_set(v___x_1079_, 1, v___x_1075_);
lean_ctor_set(v___x_1079_, 2, v___x_1077_);
lean_ctor_set(v___x_1079_, 3, v___x_1078_);
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1081_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1080_, v___x_1072_);
v___x_1082_ = l_Lean_Syntax_node2(v___x_1073_, v___x_1074_, v___x_1079_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_a_824_);
return v___x_1083_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1031_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v_quotContext_1032_; lean_object* v_currMacroScope_1033_; lean_object* v_ref_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_quotContext_1032_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1033_ = lean_ctor_get(v_a_823_, 2);
v_ref_1034_ = lean_ctor_get(v_a_823_, 5);
v___x_1035_ = l_Lean_SourceInfo_fromRef(v_ref_1034_, v___x_1011_);
v___x_1036_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1037_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1038_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_1033_, 2);
lean_inc_n(v_quotContext_1032_, 2);
v___x_1039_ = l_Lean_addMacroScope(v_quotContext_1032_, v___x_1038_, v_currMacroScope_1033_);
v___x_1040_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1035_, 10);
v___x_1041_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1035_);
lean_ctor_set(v___x_1041_, 1, v___x_1037_);
lean_ctor_set(v___x_1041_, 2, v___x_1039_);
lean_ctor_set(v___x_1041_, 3, v___x_1040_);
v___x_1042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1043_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_1044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_1045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
v___x_1046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1035_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_1048_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_1049_ = lean_box(0);
v___x_1050_ = l_Lean_addMacroScope(v_quotContext_1032_, v___x_1049_, v_currMacroScope_1033_);
v___x_1051_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_1052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1035_);
lean_ctor_set(v___x_1052_, 1, v___x_1048_);
lean_ctor_set(v___x_1052_, 2, v___x_1050_);
lean_ctor_set(v___x_1052_, 3, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_node1(v___x_1035_, v___x_1047_, v___x_1052_);
v___x_1054_ = l_Lean_Syntax_node2(v___x_1035_, v___x_1044_, v___x_1046_, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1056_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1035_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_Syntax_node2(v___x_1035_, v___x_1055_, v___x_1057_, v___x_1030_);
v___x_1059_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1035_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node3(v___x_1035_, v___x_1043_, v___x_1054_, v___x_1058_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node1(v___x_1035_, v___x_1042_, v___x_1061_);
v___x_1063_ = l_Lean_Syntax_node2(v___x_1035_, v___x_1036_, v___x_1041_, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_a_824_);
return v___x_1064_;
}
}
}
else
{
lean_object* v___x_1084_; 
lean_dec(v___x_1010_);
v___x_1084_ = l_Lean_Syntax_getArg(v___x_830_, v___x_829_);
if (v___x_841_ == 0)
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_Json_json_x2d____1___closed__3));
lean_inc(v___x_1084_);
v___x_1101_ = l_Lean_Syntax_isOfKind(v___x_1084_, v___x_1100_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; 
lean_dec(v___x_1084_);
v___x_1102_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
lean_dec(v___x_830_);
v___x_1103_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_1103_;
}
else
{
lean_object* v_quotContext_1104_; lean_object* v_currMacroScope_1105_; lean_object* v_ref_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_quotContext_1104_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1105_ = lean_ctor_get(v_a_823_, 2);
v_ref_1106_ = lean_ctor_get(v_a_823_, 5);
v___x_1107_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_1108_ = l_Lean_SourceInfo_fromRef(v_ref_1106_, v___x_841_);
v___x_1109_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1110_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1111_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1105_);
lean_inc(v_quotContext_1104_);
v___x_1112_ = l_Lean_addMacroScope(v_quotContext_1104_, v___x_1111_, v_currMacroScope_1105_);
v___x_1113_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1108_, 2);
v___x_1114_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1108_);
lean_ctor_set(v___x_1114_, 1, v___x_1110_);
lean_ctor_set(v___x_1114_, 2, v___x_1112_);
lean_ctor_set(v___x_1114_, 3, v___x_1113_);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1116_ = l_Lean_Syntax_node1(v___x_1108_, v___x_1115_, v___x_1107_);
v___x_1117_ = l_Lean_Syntax_node2(v___x_1108_, v___x_1109_, v___x_1114_, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_a_824_);
return v___x_1118_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1085_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1085_;
}
v___jp_1085_:
{
lean_object* v_quotContext_1086_; lean_object* v_currMacroScope_1087_; lean_object* v_ref_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_quotContext_1086_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1087_ = lean_ctor_get(v_a_823_, 2);
v_ref_1088_ = lean_ctor_get(v_a_823_, 5);
v___x_1089_ = l_Lean_SourceInfo_fromRef(v_ref_1088_, v___x_841_);
v___x_1090_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1091_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1092_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1087_);
lean_inc(v_quotContext_1086_);
v___x_1093_ = l_Lean_addMacroScope(v_quotContext_1086_, v___x_1092_, v_currMacroScope_1087_);
v___x_1094_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1089_, 2);
v___x_1095_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1089_);
lean_ctor_set(v___x_1095_, 1, v___x_1091_);
lean_ctor_set(v___x_1095_, 2, v___x_1093_);
lean_ctor_set(v___x_1095_, 3, v___x_1094_);
v___x_1096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1097_ = l_Lean_Syntax_node1(v___x_1089_, v___x_1096_, v___x_1084_);
v___x_1098_ = l_Lean_Syntax_node2(v___x_1089_, v___x_1090_, v___x_1095_, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_a_824_);
return v___x_1099_;
}
}
}
v___jp_844_:
{
size_t v_sz_846_; size_t v___x_847_; lean_object* v___x_848_; 
v_sz_846_ = lean_array_size(v___y_845_);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_846_, v___x_847_, v___y_845_);
if (lean_obj_tag(v___x_848_) == 0)
{
uint8_t v___x_849_; 
v___x_849_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v___x_830_);
v___x_850_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_850_;
}
else
{
lean_object* v_quotContext_851_; lean_object* v_currMacroScope_852_; lean_object* v_ref_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_quotContext_851_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_852_ = lean_ctor_get(v_a_823_, 2);
v_ref_853_ = lean_ctor_get(v_a_823_, 5);
v___x_854_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_855_ = l_Lean_SourceInfo_fromRef(v_ref_853_, v___x_843_);
v___x_856_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_857_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_858_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
v___x_859_ = l_Lean_addMacroScope(v_quotContext_851_, v___x_858_, v_currMacroScope_852_);
v___x_860_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_855_, 2);
v___x_861_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_861_, 0, v___x_855_);
lean_ctor_set(v___x_861_, 1, v___x_857_);
lean_ctor_set(v___x_861_, 2, v___x_859_);
lean_ctor_set(v___x_861_, 3, v___x_860_);
v___x_862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_863_ = l_Lean_Syntax_node1(v___x_855_, v___x_862_, v___x_854_);
v___x_864_ = l_Lean_Syntax_node2(v___x_855_, v___x_856_, v___x_861_, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_a_824_);
return v___x_865_;
}
}
else
{
lean_object* v_val_866_; lean_object* v_quotContext_867_; lean_object* v_currMacroScope_868_; lean_object* v_ref_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; size_t v_sz_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v___x_830_);
v_val_866_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v___x_848_, 1);
v_quotContext_867_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_868_ = lean_ctor_get(v_a_823_, 2);
v_ref_869_ = lean_ctor_get(v_a_823_, 5);
v___x_870_ = l_Lean_SourceInfo_fromRef(v_ref_869_, v___x_843_);
v___x_871_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_872_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11);
v___x_873_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13));
lean_inc(v_currMacroScope_868_);
lean_inc(v_quotContext_867_);
v___x_874_ = l_Lean_addMacroScope(v_quotContext_867_, v___x_873_, v_currMacroScope_868_);
v___x_875_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17));
lean_inc_n(v___x_870_, 7);
v___x_876_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_876_, 0, v___x_870_);
lean_ctor_set(v___x_876_, 1, v___x_872_);
lean_ctor_set(v___x_876_, 2, v___x_874_);
lean_ctor_set(v___x_876_, 3, v___x_875_);
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_878_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19));
v___x_879_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20));
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_870_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
v_sz_882_ = lean_array_size(v_val_866_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v___x_870_, v_sz_882_, v___x_847_, v_val_866_);
v___x_884_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
v___x_885_ = l_Lean_mkSepArray(v___x_883_, v___x_884_);
lean_dec_ref(v___x_883_);
v___x_886_ = l_Array_append___redArg(v___x_881_, v___x_885_);
lean_dec_ref(v___x_885_);
v___x_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_887_, 0, v___x_870_);
lean_ctor_set(v___x_887_, 1, v___x_877_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
v___x_888_ = ((lean_object*)(l_Lean_Json_json_x5b___x5d___closed__9));
v___x_889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_870_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_Syntax_node3(v___x_870_, v___x_878_, v___x_880_, v___x_887_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node1(v___x_870_, v___x_877_, v___x_890_);
v___x_892_ = l_Lean_Syntax_node2(v___x_870_, v___x_871_, v___x_876_, v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_a_824_);
return v___x_893_;
}
}
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = l_Lean_Syntax_getArg(v___x_830_, v___x_837_);
lean_inc(v___x_1119_);
v___x_1120_ = l_Lean_Syntax_matchesNull(v___x_1119_, v___x_837_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_Syntax_matchesNull(v___x_1119_, v___x_829_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; 
v___x_1122_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec(v___x_830_);
v___x_1123_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_1123_;
}
else
{
lean_object* v_quotContext_1124_; lean_object* v_currMacroScope_1125_; lean_object* v_ref_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_quotContext_1124_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1125_ = lean_ctor_get(v_a_823_, 2);
v_ref_1126_ = lean_ctor_get(v_a_823_, 5);
v___x_1127_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_1128_ = l_Lean_SourceInfo_fromRef(v_ref_1126_, v___x_1121_);
v___x_1129_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1130_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1131_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1125_);
lean_inc(v_quotContext_1124_);
v___x_1132_ = l_Lean_addMacroScope(v_quotContext_1124_, v___x_1131_, v_currMacroScope_1125_);
v___x_1133_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1128_, 2);
v___x_1134_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1128_);
lean_ctor_set(v___x_1134_, 1, v___x_1130_);
lean_ctor_set(v___x_1134_, 2, v___x_1132_);
lean_ctor_set(v___x_1134_, 3, v___x_1133_);
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1136_ = l_Lean_Syntax_node1(v___x_1128_, v___x_1135_, v___x_1127_);
v___x_1137_ = l_Lean_Syntax_node2(v___x_1128_, v___x_1129_, v___x_1134_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_a_824_);
return v___x_1138_;
}
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Syntax_getArg(v___x_830_, v___x_829_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1139_);
v___x_1175_ = l_Lean_Syntax_isOfKind(v___x_1139_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint8_t v___x_1176_; 
lean_dec(v___x_1139_);
v___x_1176_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec(v___x_830_);
v___x_1177_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_1177_;
}
else
{
lean_object* v_quotContext_1178_; lean_object* v_currMacroScope_1179_; lean_object* v_ref_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_quotContext_1178_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1179_ = lean_ctor_get(v_a_823_, 2);
v_ref_1180_ = lean_ctor_get(v_a_823_, 5);
v___x_1181_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_1182_ = l_Lean_SourceInfo_fromRef(v_ref_1180_, v___x_1120_);
v___x_1183_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1184_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1185_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1179_);
lean_inc(v_quotContext_1178_);
v___x_1186_ = l_Lean_addMacroScope(v_quotContext_1178_, v___x_1185_, v_currMacroScope_1179_);
v___x_1187_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1182_, 2);
v___x_1188_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1182_);
lean_ctor_set(v___x_1188_, 1, v___x_1184_);
lean_ctor_set(v___x_1188_, 2, v___x_1186_);
lean_ctor_set(v___x_1188_, 3, v___x_1187_);
v___x_1189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1190_ = l_Lean_Syntax_node1(v___x_1182_, v___x_1189_, v___x_1181_);
v___x_1191_ = l_Lean_Syntax_node2(v___x_1182_, v___x_1183_, v___x_1188_, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_a_824_);
return v___x_1192_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1140_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1140_;
}
v___jp_1140_:
{
lean_object* v_quotContext_1141_; lean_object* v_currMacroScope_1142_; lean_object* v_ref_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_quotContext_1141_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1142_ = lean_ctor_get(v_a_823_, 2);
v_ref_1143_ = lean_ctor_get(v_a_823_, 5);
v___x_1144_ = l_Lean_SourceInfo_fromRef(v_ref_1143_, v___x_1120_);
v___x_1145_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1146_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1147_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc_n(v_currMacroScope_1142_, 2);
lean_inc_n(v_quotContext_1141_, 2);
v___x_1148_ = l_Lean_addMacroScope(v_quotContext_1141_, v___x_1147_, v_currMacroScope_1142_);
v___x_1149_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1144_, 10);
v___x_1150_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1144_);
lean_ctor_set(v___x_1150_, 1, v___x_1146_);
lean_ctor_set(v___x_1150_, 2, v___x_1148_);
lean_ctor_set(v___x_1150_, 3, v___x_1149_);
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1152_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40));
v___x_1153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__4));
v___x_1154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__5));
v___x_1155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1144_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__7));
v___x_1157_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__9);
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Lean_addMacroScope(v_quotContext_1141_, v___x_1158_, v_currMacroScope_1142_);
v___x_1160_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41));
v___x_1161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1144_);
lean_ctor_set(v___x_1161_, 1, v___x_1157_);
lean_ctor_set(v___x_1161_, 2, v___x_1159_);
lean_ctor_set(v___x_1161_, 3, v___x_1160_);
v___x_1162_ = l_Lean_Syntax_node1(v___x_1144_, v___x_1156_, v___x_1161_);
v___x_1163_ = l_Lean_Syntax_node2(v___x_1144_, v___x_1153_, v___x_1155_, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43));
v___x_1165_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__4));
v___x_1166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1144_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_Syntax_node2(v___x_1144_, v___x_1164_, v___x_1166_, v___x_1139_);
v___x_1168_ = ((lean_object*)(l_Lean_Json_json_quot___closed__13));
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1144_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_Syntax_node3(v___x_1144_, v___x_1152_, v___x_1163_, v___x_1167_, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_node1(v___x_1144_, v___x_1151_, v___x_1170_);
v___x_1172_ = l_Lean_Syntax_node2(v___x_1144_, v___x_1145_, v___x_1150_, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_a_824_);
return v___x_1173_;
}
}
}
else
{
lean_object* v___x_1193_; 
lean_dec(v___x_1119_);
v___x_1193_ = l_Lean_Syntax_getArg(v___x_830_, v___x_829_);
if (v___x_839_ == 0)
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_Json_json_x2d___00__closed__8));
lean_inc(v___x_1193_);
v___x_1210_ = l_Lean_Syntax_isOfKind(v___x_1193_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint8_t v___x_1211_; 
lean_dec(v___x_1193_);
v___x_1211_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
lean_dec(v___x_830_);
v___x_1212_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_1212_;
}
else
{
lean_object* v_quotContext_1213_; lean_object* v_currMacroScope_1214_; lean_object* v_ref_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_quotContext_1213_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1214_ = lean_ctor_get(v_a_823_, 2);
v_ref_1215_ = lean_ctor_get(v_a_823_, 5);
v___x_1216_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_1217_ = l_Lean_SourceInfo_fromRef(v_ref_1215_, v___x_839_);
v___x_1218_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1219_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1220_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1214_);
lean_inc(v_quotContext_1213_);
v___x_1221_ = l_Lean_addMacroScope(v_quotContext_1213_, v___x_1220_, v_currMacroScope_1214_);
v___x_1222_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1217_, 2);
v___x_1223_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1217_);
lean_ctor_set(v___x_1223_, 1, v___x_1219_);
lean_ctor_set(v___x_1223_, 2, v___x_1221_);
lean_ctor_set(v___x_1223_, 3, v___x_1222_);
v___x_1224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1225_ = l_Lean_Syntax_node1(v___x_1217_, v___x_1224_, v___x_1216_);
v___x_1226_ = l_Lean_Syntax_node2(v___x_1217_, v___x_1218_, v___x_1223_, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_a_824_);
return v___x_1227_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1194_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1194_;
}
v___jp_1194_:
{
lean_object* v_quotContext_1195_; lean_object* v_currMacroScope_1196_; lean_object* v_ref_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_quotContext_1195_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1196_ = lean_ctor_get(v_a_823_, 2);
v_ref_1197_ = lean_ctor_get(v_a_823_, 5);
v___x_1198_ = l_Lean_SourceInfo_fromRef(v_ref_1197_, v___x_839_);
v___x_1199_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1200_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
v___x_1201_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34));
lean_inc(v_currMacroScope_1196_);
lean_inc(v_quotContext_1195_);
v___x_1202_ = l_Lean_addMacroScope(v_quotContext_1195_, v___x_1201_, v_currMacroScope_1196_);
v___x_1203_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38));
lean_inc_n(v___x_1198_, 2);
v___x_1204_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1198_);
lean_ctor_set(v___x_1204_, 1, v___x_1200_);
lean_ctor_set(v___x_1204_, 2, v___x_1202_);
lean_ctor_set(v___x_1204_, 3, v___x_1203_);
v___x_1205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1206_ = l_Lean_Syntax_node1(v___x_1198_, v___x_1205_, v___x_1193_);
v___x_1207_ = l_Lean_Syntax_node2(v___x_1198_, v___x_1199_, v___x_1204_, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v_a_824_);
return v___x_1208_;
}
}
}
}
else
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Syntax_getArg(v___x_830_, v___x_837_);
if (v___x_836_ == 0)
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_Json_json___00__closed__3));
lean_inc(v___x_1228_);
v___x_1245_ = l_Lean_Syntax_isOfKind(v___x_1228_, v___x_1244_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; 
lean_dec(v___x_1228_);
v___x_1246_ = l_Lean_Syntax_isAntiquot(v___x_830_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_dec(v___x_830_);
v___x_1247_ = l_Lean_Macro_throwUnsupported___redArg(v_a_824_);
return v___x_1247_;
}
else
{
lean_object* v_quotContext_1248_; lean_object* v_currMacroScope_1249_; lean_object* v_ref_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_quotContext_1248_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1249_ = lean_ctor_get(v_a_823_, 2);
v_ref_1250_ = lean_ctor_get(v_a_823_, 5);
v___x_1251_ = l_Lean_Syntax_getAntiquotTerm(v___x_830_);
lean_dec(v___x_830_);
v___x_1252_ = l_Lean_SourceInfo_fromRef(v_ref_1250_, v___x_836_);
v___x_1253_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1254_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
v___x_1255_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5));
lean_inc(v_currMacroScope_1249_);
lean_inc(v_quotContext_1248_);
v___x_1256_ = l_Lean_addMacroScope(v_quotContext_1248_, v___x_1255_, v_currMacroScope_1249_);
v___x_1257_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9));
lean_inc_n(v___x_1252_, 2);
v___x_1258_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1252_);
lean_ctor_set(v___x_1258_, 1, v___x_1254_);
lean_ctor_set(v___x_1258_, 2, v___x_1256_);
lean_ctor_set(v___x_1258_, 3, v___x_1257_);
v___x_1259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1260_ = l_Lean_Syntax_node1(v___x_1252_, v___x_1259_, v___x_1251_);
v___x_1261_ = l_Lean_Syntax_node2(v___x_1252_, v___x_1253_, v___x_1258_, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_a_824_);
return v___x_1262_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1229_;
}
}
else
{
lean_dec(v___x_830_);
goto v___jp_1229_;
}
v___jp_1229_:
{
lean_object* v_quotContext_1230_; lean_object* v_currMacroScope_1231_; lean_object* v_ref_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_quotContext_1230_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1231_ = lean_ctor_get(v_a_823_, 2);
v_ref_1232_ = lean_ctor_get(v_a_823_, 5);
v___x_1233_ = l_Lean_SourceInfo_fromRef(v_ref_1232_, v___x_836_);
v___x_1234_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1235_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45);
v___x_1236_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46));
lean_inc(v_currMacroScope_1231_);
lean_inc(v_quotContext_1230_);
v___x_1237_ = l_Lean_addMacroScope(v_quotContext_1230_, v___x_1236_, v_currMacroScope_1231_);
v___x_1238_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50));
lean_inc_n(v___x_1233_, 2);
v___x_1239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1233_);
lean_ctor_set(v___x_1239_, 1, v___x_1235_);
lean_ctor_set(v___x_1239_, 2, v___x_1237_);
lean_ctor_set(v___x_1239_, 3, v___x_1238_);
v___x_1240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1241_ = l_Lean_Syntax_node1(v___x_1233_, v___x_1240_, v___x_1228_);
v___x_1242_ = l_Lean_Syntax_node2(v___x_1233_, v___x_1234_, v___x_1239_, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_824_);
return v___x_1243_;
}
}
}
else
{
lean_object* v_quotContext_1263_; lean_object* v_currMacroScope_1264_; lean_object* v_ref_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v___x_830_);
v_quotContext_1263_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1264_ = lean_ctor_get(v_a_823_, 2);
v_ref_1265_ = lean_ctor_get(v_a_823_, 5);
v___x_1266_ = l_Lean_SourceInfo_fromRef(v_ref_1265_, v___x_834_);
v___x_1267_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1268_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1269_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1264_, 2);
lean_inc_n(v_quotContext_1263_, 2);
v___x_1270_ = l_Lean_addMacroScope(v_quotContext_1263_, v___x_1269_, v_currMacroScope_1264_);
v___x_1271_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1266_, 3);
v___x_1272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1266_);
lean_ctor_set(v___x_1272_, 1, v___x_1268_);
lean_ctor_set(v___x_1272_, 2, v___x_1270_);
lean_ctor_set(v___x_1272_, 3, v___x_1271_);
v___x_1273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1274_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60);
v___x_1275_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62));
v___x_1276_ = l_Lean_addMacroScope(v_quotContext_1263_, v___x_1275_, v_currMacroScope_1264_);
v___x_1277_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66));
v___x_1278_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1266_);
lean_ctor_set(v___x_1278_, 1, v___x_1274_);
lean_ctor_set(v___x_1278_, 2, v___x_1276_);
lean_ctor_set(v___x_1278_, 3, v___x_1277_);
v___x_1279_ = l_Lean_Syntax_node1(v___x_1266_, v___x_1273_, v___x_1278_);
v___x_1280_ = l_Lean_Syntax_node2(v___x_1266_, v___x_1267_, v___x_1272_, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_a_824_);
return v___x_1281_;
}
}
else
{
lean_object* v_quotContext_1282_; lean_object* v_currMacroScope_1283_; lean_object* v_ref_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v___x_830_);
v_quotContext_1282_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1283_ = lean_ctor_get(v_a_823_, 2);
v_ref_1284_ = lean_ctor_get(v_a_823_, 5);
v___x_1285_ = l_Lean_SourceInfo_fromRef(v_ref_1284_, v___x_832_);
v___x_1286_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1));
v___x_1287_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
v___x_1288_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54));
lean_inc_n(v_currMacroScope_1283_, 2);
lean_inc_n(v_quotContext_1282_, 2);
v___x_1289_ = l_Lean_addMacroScope(v_quotContext_1282_, v___x_1288_, v_currMacroScope_1283_);
v___x_1290_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58));
lean_inc_n(v___x_1285_, 3);
v___x_1291_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1285_);
lean_ctor_set(v___x_1291_, 1, v___x_1287_);
lean_ctor_set(v___x_1291_, 2, v___x_1289_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___closed__0));
v___x_1293_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68);
v___x_1294_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69));
v___x_1295_ = l_Lean_addMacroScope(v_quotContext_1282_, v___x_1294_, v_currMacroScope_1283_);
v___x_1296_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73));
v___x_1297_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1285_);
lean_ctor_set(v___x_1297_, 1, v___x_1293_);
lean_ctor_set(v___x_1297_, 2, v___x_1295_);
lean_ctor_set(v___x_1297_, 3, v___x_1296_);
v___x_1298_ = l_Lean_Syntax_node1(v___x_1285_, v___x_1292_, v___x_1297_);
v___x_1299_ = l_Lean_Syntax_node2(v___x_1285_, v___x_1286_, v___x_1291_, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v_a_824_);
return v___x_1300_;
}
}
else
{
lean_object* v_quotContext_1301_; lean_object* v_currMacroScope_1302_; lean_object* v_ref_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v___x_830_);
v_quotContext_1301_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_1302_ = lean_ctor_get(v_a_823_, 2);
v_ref_1303_ = lean_ctor_get(v_a_823_, 5);
v___x_1304_ = 0;
v___x_1305_ = l_Lean_SourceInfo_fromRef(v_ref_1303_, v___x_1304_);
v___x_1306_ = lean_obj_once(&l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75, &l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75_once, _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75);
v___x_1307_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76));
lean_inc(v_currMacroScope_1302_);
lean_inc(v_quotContext_1301_);
v___x_1308_ = l_Lean_addMacroScope(v_quotContext_1301_, v___x_1307_, v_currMacroScope_1302_);
v___x_1309_ = ((lean_object*)(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80));
v___x_1310_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1305_);
lean_ctor_set(v___x_1310_, 1, v___x_1306_);
lean_ctor_set(v___x_1310_, 2, v___x_1308_);
lean_ctor_set(v___x_1310_, 3, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_a_824_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___boxed(lean_object* v_x_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(v_x_1312_, v_a_1313_, v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1315_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5(uint8_t v___x_1316_, size_t v_sz_1317_, size_t v_i_1318_, lean_object* v_bs_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___redArg(v___x_1316_, v_sz_1317_, v_i_1318_, v_bs_1319_, v___y_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1316_ = stack[0].m_num;
size_t v_sz_1317_ = stack[1].m_num;
size_t v_i_1318_ = stack[2].m_num;
lean_object* v_bs_1319_ = stack[3].m_obj;
lean_object* v___y_1320_ = stack[4].m_obj;
lean_object* v___y_1321_ = stack[5].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5(v___x_1316_, v_sz_1317_, v_i_1318_, v_bs_1319_, v___y_1320_, v___y_1321_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5___boxed(lean_object* v___x_1324_, lean_object* v_sz_1325_, lean_object* v_i_1326_, lean_object* v_bs_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___x_35922__boxed_1330_; size_t v_sz_boxed_1331_; size_t v_i_boxed_1332_; lean_object* v_res_1333_; 
v___x_35922__boxed_1330_ = lean_unbox(v___x_1324_);
v_sz_boxed_1331_ = lean_unbox_usize(v_sz_1325_);
lean_dec(v_sz_1325_);
v_i_boxed_1332_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_res_1333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5_spec__5(v___x_35922__boxed_1330_, v_sz_boxed_1331_, v_i_boxed_1332_, v_bs_1327_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
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
