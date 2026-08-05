// Lean compiler output
// Module: Std.Internal.Do.ExceptPost
// Imports: public import Std.Internal.Do.Assertion
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_instPartialOrderNil;
LEAN_EXPORT lean_object* l_Std_Internal_Do_instCompleteLatticeNil;
LEAN_EXPORT lean_object* l_Std_Internal_Do_instPartialOrderCons(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_instCompleteLatticeCons(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "termEPost⟨_⟩"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_2),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(154, 25, 148, 55, 111, 160, 202, 71)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 6, .m_data = "EPost⟨"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7_value)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13_value)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16_value;
static const lean_string_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17_value)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19_value;
static const lean_ctor_object l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19_value)}};
static const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_termEPost_u27e8___u27e9 = (const lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20_value;
static const lean_string_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "termEpost⟨_⟩"};
static const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 191, 145, 121, 242, 68, 46, 80)}};
static const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value;
static const lean_string_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 6, .m_data = "epost⟨"};
static const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2_value)}};
static const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value),((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value)}};
static const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value),((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4_value),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value)}};
static const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5_value)}};
static const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_termEpost_u27e8___u27e9 = (const lean_object*)&l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "EPost.Cons"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(83, 155, 62, 138, 95, 156, 114, 0)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 182, 16, 6, 247, 146, 42, 70)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EPost.Nil"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nil"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(165, 88, 72, 137, 136, 21, 70, 169)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(59, 100, 61, 2, 11, 215, 128, 128)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "EPost.Cons.mk"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(83, 155, 62, 138, 95, 156, 114, 0)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 114, 53, 121, 148, 172, 128, 92)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 182, 16, 6, 247, 146, 42, 70)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_4),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 64, 94, 8, 151, 53, 87, 57)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "EPost.Nil.mk"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(165, 88, 72, 137, 136, 21, 70, 169)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 118, 194, 97, 192, 172, 108, 81)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(59, 100, 61, 2, 11, 215, 128, 128)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_4),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(95, 86, 143, 247, 183, 225, 187, 94)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_unexpandEPostCons___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_fakeMod"};
static const lean_object* l_Std_Internal_Do_unexpandEPostCons___closed__0 = (const lean_object*)&l_Std_Internal_Do_unexpandEPostCons___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_unexpandEPostCons___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_unexpandEPostCons___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 44, 241, 255, 153, 255, 67, 53)}};
static const lean_object* l_Std_Internal_Do_unexpandEPostCons___closed__1 = (const lean_object*)&l_Std_Internal_Do_unexpandEPostCons___closed__1_value;
static lean_once_cell_t l_Std_Internal_Do_unexpandEPostCons___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do_unexpandEPostCons___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do_unexpandEPostConsMk___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Internal_Do_instPartialOrderNil(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Std_Internal_Do_instCompleteLatticeNil(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instPartialOrderCons(lean_object* v_eh_3_, lean_object* v_et_4_, lean_object* v_inst_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instCompleteLatticeCons(lean_object* v_eh_8_, lean_object* v_et_9_, lean_object* v_inst_10_, lean_object* v_inst_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7));
v___x_95_ = l_String_toRawSubstring_x27(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Array_mkArray0(lean_box(0));
return v___x_118_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18));
v___x_121_ = l_String_toRawSubstring_x27(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
lean_inc(v_x_143_);
v___x_147_ = l_Lean_Syntax_isOfKind(v_x_143_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_x_143_);
v___x_148_ = lean_box(1);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_145_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = l_Lean_Syntax_getArg(v_x_143_, v___x_151_);
lean_dec(v_x_143_);
lean_inc(v___x_152_);
v___x_153_ = l_Lean_Syntax_matchesNull(v___x_152_, v___x_150_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; 
lean_inc(v___x_152_);
v___x_154_ = l_Lean_Syntax_matchesNull(v___x_152_, v___x_151_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(2u);
v___x_156_ = l_Lean_Syntax_getNumArgs(v___x_152_);
v___x_157_ = lean_nat_dec_le(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v___x_156_);
lean_dec(v___x_152_);
v___x_158_ = lean_box(1);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_a_145_);
return v___x_159_;
}
else
{
lean_object* v_quotContext_160_; lean_object* v_currMacroScope_161_; lean_object* v_ref_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_quotContext_160_ = lean_ctor_get(v_a_144_, 1);
v_currMacroScope_161_ = lean_ctor_get(v_a_144_, 2);
v_ref_162_ = lean_ctor_get(v_a_144_, 5);
v___x_163_ = l_Lean_Syntax_getArg(v___x_152_, v___x_150_);
v___x_164_ = l_Lean_Syntax_getArgs(v___x_152_);
lean_dec(v___x_152_);
v___x_165_ = l_Array_extract___redArg(v___x_164_, v___x_155_, v___x_156_);
lean_dec_ref(v___x_164_);
v___x_166_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_167_ = lean_box(2);
v___x_168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_165_);
v___x_169_ = l_Lean_Syntax_getArgs(v___x_168_);
lean_dec_ref_known(v___x_168_, 3);
v___x_170_ = l_Lean_SourceInfo_fromRef(v_ref_162_, v___x_154_);
v___x_171_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_172_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_173_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
lean_inc(v_currMacroScope_161_);
lean_inc(v_quotContext_160_);
v___x_174_ = l_Lean_addMacroScope(v_quotContext_160_, v___x_173_, v_currMacroScope_161_);
v___x_175_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_170_, 6);
v___x_176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_176_, 0, v___x_170_);
lean_ctor_set(v___x_176_, 1, v___x_172_);
lean_ctor_set(v___x_176_, 2, v___x_174_);
lean_ctor_set(v___x_176_, 3, v___x_175_);
v___x_177_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
v___x_178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_170_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_180_ = l_Array_append___redArg(v___x_179_, v___x_169_);
lean_dec_ref(v___x_169_);
v___x_181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_181_, 0, v___x_170_);
lean_ctor_set(v___x_181_, 1, v___x_166_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
v___x_182_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_170_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_Syntax_node3(v___x_170_, v___x_146_, v___x_178_, v___x_181_, v___x_183_);
v___x_185_ = l_Lean_Syntax_node2(v___x_170_, v___x_166_, v___x_163_, v___x_184_);
v___x_186_ = l_Lean_Syntax_node2(v___x_170_, v___x_171_, v___x_176_, v___x_185_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_a_145_);
return v___x_187_;
}
}
else
{
lean_object* v_quotContext_188_; lean_object* v_currMacroScope_189_; lean_object* v_ref_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_quotContext_188_ = lean_ctor_get(v_a_144_, 1);
v_currMacroScope_189_ = lean_ctor_get(v_a_144_, 2);
v_ref_190_ = lean_ctor_get(v_a_144_, 5);
v___x_191_ = l_Lean_Syntax_getArg(v___x_152_, v___x_150_);
lean_dec(v___x_152_);
v___x_192_ = l_Lean_SourceInfo_fromRef(v_ref_190_, v___x_153_);
v___x_193_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_194_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_195_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
lean_inc_n(v_currMacroScope_189_, 2);
lean_inc_n(v_quotContext_188_, 2);
v___x_196_ = l_Lean_addMacroScope(v_quotContext_188_, v___x_195_, v_currMacroScope_189_);
v___x_197_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_192_, 3);
v___x_198_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_198_, 0, v___x_192_);
lean_ctor_set(v___x_198_, 1, v___x_194_);
lean_ctor_set(v___x_198_, 2, v___x_196_);
lean_ctor_set(v___x_198_, 3, v___x_197_);
v___x_199_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_200_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
v___x_201_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21));
v___x_202_ = l_Lean_addMacroScope(v_quotContext_188_, v___x_201_, v_currMacroScope_189_);
v___x_203_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26));
v___x_204_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_204_, 0, v___x_192_);
lean_ctor_set(v___x_204_, 1, v___x_200_);
lean_ctor_set(v___x_204_, 2, v___x_202_);
lean_ctor_set(v___x_204_, 3, v___x_203_);
v___x_205_ = l_Lean_Syntax_node2(v___x_192_, v___x_199_, v___x_191_, v___x_204_);
v___x_206_ = l_Lean_Syntax_node2(v___x_192_, v___x_193_, v___x_198_, v___x_205_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_a_145_);
return v___x_207_;
}
}
else
{
lean_object* v_quotContext_208_; lean_object* v_currMacroScope_209_; lean_object* v_ref_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v___x_152_);
v_quotContext_208_ = lean_ctor_get(v_a_144_, 1);
v_currMacroScope_209_ = lean_ctor_get(v_a_144_, 2);
v_ref_210_ = lean_ctor_get(v_a_144_, 5);
v___x_211_ = 0;
v___x_212_ = l_Lean_SourceInfo_fromRef(v_ref_210_, v___x_211_);
v___x_213_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
v___x_214_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21));
lean_inc(v_currMacroScope_209_);
lean_inc(v_quotContext_208_);
v___x_215_ = l_Lean_addMacroScope(v_quotContext_208_, v___x_214_, v_currMacroScope_209_);
v___x_216_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26));
v___x_217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_217_, 0, v___x_212_);
lean_ctor_set(v___x_217_, 1, v___x_213_);
lean_ctor_set(v___x_217_, 2, v___x_215_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_a_145_);
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___boxed(lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(v_x_219_, v_a_220_, v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_222_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0));
v___x_225_ = l_String_toRawSubstring_x27(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9));
v___x_251_ = l_String_toRawSubstring_x27(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(lean_object* v_x_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
lean_inc(v_x_274_);
v___x_278_ = l_Lean_Syntax_isOfKind(v_x_274_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v_x_274_);
v___x_279_ = lean_box(1);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_a_276_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = l_Lean_Syntax_getArg(v_x_274_, v___x_282_);
lean_dec(v_x_274_);
lean_inc(v___x_283_);
v___x_284_ = l_Lean_Syntax_matchesNull(v___x_283_, v___x_281_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_inc(v___x_283_);
v___x_285_ = l_Lean_Syntax_matchesNull(v___x_283_, v___x_282_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_unsigned_to_nat(2u);
v___x_287_ = l_Lean_Syntax_getNumArgs(v___x_283_);
v___x_288_ = lean_nat_dec_le(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v___x_287_);
lean_dec(v___x_283_);
v___x_289_ = lean_box(1);
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_a_276_);
return v___x_290_;
}
else
{
lean_object* v_quotContext_291_; lean_object* v_currMacroScope_292_; lean_object* v_ref_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_quotContext_291_ = lean_ctor_get(v_a_275_, 1);
v_currMacroScope_292_ = lean_ctor_get(v_a_275_, 2);
v_ref_293_ = lean_ctor_get(v_a_275_, 5);
v___x_294_ = l_Lean_Syntax_getArg(v___x_283_, v___x_281_);
v___x_295_ = l_Lean_Syntax_getArgs(v___x_283_);
lean_dec(v___x_283_);
v___x_296_ = l_Array_extract___redArg(v___x_295_, v___x_286_, v___x_287_);
lean_dec_ref(v___x_295_);
v___x_297_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_298_ = lean_box(2);
v___x_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_ctor_set(v___x_299_, 2, v___x_296_);
v___x_300_ = l_Lean_Syntax_getArgs(v___x_299_);
lean_dec_ref_known(v___x_299_, 3);
v___x_301_ = l_Lean_SourceInfo_fromRef(v_ref_293_, v___x_285_);
v___x_302_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_303_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_304_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
lean_inc(v_currMacroScope_292_);
lean_inc(v_quotContext_291_);
v___x_305_ = l_Lean_addMacroScope(v_quotContext_291_, v___x_304_, v_currMacroScope_292_);
v___x_306_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_301_, 6);
v___x_307_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_307_, 0, v___x_301_);
lean_ctor_set(v___x_307_, 1, v___x_303_);
lean_ctor_set(v___x_307_, 2, v___x_305_);
lean_ctor_set(v___x_307_, 3, v___x_306_);
v___x_308_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
v___x_309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_301_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_311_ = l_Array_append___redArg(v___x_310_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_301_);
lean_ctor_set(v___x_312_, 1, v___x_297_);
lean_ctor_set(v___x_312_, 2, v___x_311_);
v___x_313_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_301_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_Syntax_node3(v___x_301_, v___x_277_, v___x_309_, v___x_312_, v___x_314_);
v___x_316_ = l_Lean_Syntax_node2(v___x_301_, v___x_297_, v___x_294_, v___x_315_);
v___x_317_ = l_Lean_Syntax_node2(v___x_301_, v___x_302_, v___x_307_, v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_a_276_);
return v___x_318_;
}
}
else
{
lean_object* v_quotContext_319_; lean_object* v_currMacroScope_320_; lean_object* v_ref_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_quotContext_319_ = lean_ctor_get(v_a_275_, 1);
v_currMacroScope_320_ = lean_ctor_get(v_a_275_, 2);
v_ref_321_ = lean_ctor_get(v_a_275_, 5);
v___x_322_ = l_Lean_Syntax_getArg(v___x_283_, v___x_281_);
lean_dec(v___x_283_);
v___x_323_ = l_Lean_SourceInfo_fromRef(v_ref_321_, v___x_284_);
v___x_324_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_325_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_326_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
lean_inc_n(v_currMacroScope_320_, 2);
lean_inc_n(v_quotContext_319_, 2);
v___x_327_ = l_Lean_addMacroScope(v_quotContext_319_, v___x_326_, v_currMacroScope_320_);
v___x_328_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_323_, 3);
v___x_329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_329_, 0, v___x_323_);
lean_ctor_set(v___x_329_, 1, v___x_325_);
lean_ctor_set(v___x_329_, 2, v___x_327_);
lean_ctor_set(v___x_329_, 3, v___x_328_);
v___x_330_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_331_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
v___x_332_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11));
v___x_333_ = l_Lean_addMacroScope(v_quotContext_319_, v___x_332_, v_currMacroScope_320_);
v___x_334_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16));
v___x_335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_335_, 0, v___x_323_);
lean_ctor_set(v___x_335_, 1, v___x_331_);
lean_ctor_set(v___x_335_, 2, v___x_333_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
v___x_336_ = l_Lean_Syntax_node2(v___x_323_, v___x_330_, v___x_322_, v___x_335_);
v___x_337_ = l_Lean_Syntax_node2(v___x_323_, v___x_324_, v___x_329_, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_a_276_);
return v___x_338_;
}
}
else
{
lean_object* v_quotContext_339_; lean_object* v_currMacroScope_340_; lean_object* v_ref_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v___x_283_);
v_quotContext_339_ = lean_ctor_get(v_a_275_, 1);
v_currMacroScope_340_ = lean_ctor_get(v_a_275_, 2);
v_ref_341_ = lean_ctor_get(v_a_275_, 5);
v___x_342_ = 0;
v___x_343_ = l_Lean_SourceInfo_fromRef(v_ref_341_, v___x_342_);
v___x_344_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
v___x_345_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11));
lean_inc(v_currMacroScope_340_);
lean_inc(v_quotContext_339_);
v___x_346_ = l_Lean_addMacroScope(v_quotContext_339_, v___x_345_, v_currMacroScope_340_);
v___x_347_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16));
v___x_348_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_348_, 0, v___x_343_);
lean_ctor_set(v___x_348_, 1, v___x_344_);
lean_ctor_set(v___x_348_, 2, v___x_346_);
lean_ctor_set(v___x_348_, 3, v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_276_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___boxed(lean_object* v_x_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(v_x_350_, v_a_351_, v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg(lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_356_ = 0;
v___x_357_ = l_Lean_SourceInfo_fromRef(v_a_354_, v___x_356_);
v___x_358_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
v___x_359_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_357_, 3);
v___x_360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_357_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_362_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_363_, 0, v___x_357_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
v___x_364_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_357_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l_Lean_Syntax_node3(v___x_357_, v___x_358_, v___x_360_, v___x_363_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_a_355_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg___boxed(lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_368_, v_a_369_);
lean_dec(v_a_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil(lean_object* v_x_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_372_, v_a_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___boxed(lean_object* v_x_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Internal_Do_unexpandEPostNil(v_x_375_, v_a_376_, v_a_377_);
lean_dec(v_a_376_);
lean_dec(v_x_375_);
return v_res_378_;
}
}
static lean_object* _init_l_Std_Internal_Do_unexpandEPostCons___closed__2(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
v___x_384_ = ((lean_object*)(l_Std_Internal_Do_unexpandEPostCons___closed__1));
v___x_385_ = l_Lean_addMacroScope(v___x_384_, v___x_383_, v___x_382_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons(lean_object* v_x_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
lean_inc(v_x_386_);
v___x_390_ = l_Lean_Syntax_isOfKind(v_x_386_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_x_386_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_388_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = l_Lean_Syntax_getArg(v_x_386_, v___x_393_);
lean_dec(v_x_386_);
v___x_395_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_394_);
v___x_396_ = l_Lean_Syntax_matchesNull(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_a_388_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = l_Lean_Syntax_getArg(v___x_394_, v___x_399_);
v___x_401_ = l_Lean_Syntax_getArg(v___x_394_, v___x_393_);
lean_dec(v___x_394_);
v___x_402_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
lean_inc(v___x_401_);
v___x_403_ = l_Lean_Syntax_isOfKind(v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_404_ = l_Lean_SourceInfo_fromRef(v_a_387_, v___x_403_);
v___x_405_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_406_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostCons___closed__2, &l_Std_Internal_Do_unexpandEPostCons___closed__2_once, _init_l_Std_Internal_Do_unexpandEPostCons___closed__2);
v___x_407_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_404_, 2);
v___x_408_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_408_, 0, v___x_404_);
lean_ctor_set(v___x_408_, 1, v___x_405_);
lean_ctor_set(v___x_408_, 2, v___x_406_);
lean_ctor_set(v___x_408_, 3, v___x_407_);
v___x_409_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_410_ = l_Lean_Syntax_node2(v___x_404_, v___x_409_, v___x_400_, v___x_401_);
v___x_411_ = l_Lean_Syntax_node2(v___x_404_, v___x_389_, v___x_408_, v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_a_388_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = l_Lean_Syntax_getArg(v___x_401_, v___x_393_);
lean_inc(v___x_413_);
v___x_414_ = l_Lean_Syntax_matchesNull(v___x_413_, v___x_399_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
lean_inc(v___x_413_);
v___x_415_ = l_Lean_Syntax_matchesNull(v___x_413_, v___x_393_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = l_Lean_Syntax_getNumArgs(v___x_413_);
v___x_417_ = lean_nat_dec_le(v___x_395_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v___x_416_);
lean_dec(v___x_413_);
v___x_418_ = l_Lean_SourceInfo_fromRef(v_a_387_, v___x_415_);
v___x_419_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_420_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostCons___closed__2, &l_Std_Internal_Do_unexpandEPostCons___closed__2_once, _init_l_Std_Internal_Do_unexpandEPostCons___closed__2);
v___x_421_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_418_, 2);
v___x_422_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_422_, 0, v___x_418_);
lean_ctor_set(v___x_422_, 1, v___x_419_);
lean_ctor_set(v___x_422_, 2, v___x_420_);
lean_ctor_set(v___x_422_, 3, v___x_421_);
v___x_423_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_424_ = l_Lean_Syntax_node2(v___x_418_, v___x_423_, v___x_400_, v___x_401_);
v___x_425_ = l_Lean_Syntax_node2(v___x_418_, v___x_389_, v___x_422_, v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_a_388_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v___x_401_);
v___x_427_ = l_Lean_Syntax_getArg(v___x_413_, v___x_399_);
v___x_428_ = l_Lean_Syntax_getArgs(v___x_413_);
lean_dec(v___x_413_);
v___x_429_ = l_Array_extract___redArg(v___x_428_, v___x_395_, v___x_416_);
lean_dec_ref(v___x_428_);
v___x_430_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_431_ = lean_box(2);
v___x_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_429_);
v___x_433_ = l_Lean_Syntax_getArgs(v___x_432_);
lean_dec_ref_known(v___x_432_, 3);
v___x_434_ = l_Lean_SourceInfo_fromRef(v_a_387_, v___x_415_);
v___x_435_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_434_, 4);
v___x_436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_434_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
lean_inc_ref(v___x_438_);
v___x_439_ = l_Array_mkArray4___redArg(v___x_400_, v___x_438_, v___x_427_, v___x_438_);
v___x_440_ = l_Array_append___redArg(v___x_439_, v___x_433_);
lean_dec_ref(v___x_433_);
v___x_441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_441_, 0, v___x_434_);
lean_ctor_set(v___x_441_, 1, v___x_430_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
v___x_442_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_434_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_Syntax_node3(v___x_434_, v___x_402_, v___x_436_, v___x_441_, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_a_388_);
return v___x_445_;
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v___x_401_);
v___x_446_ = l_Lean_Syntax_getArg(v___x_413_, v___x_399_);
lean_dec(v___x_413_);
v___x_447_ = l_Lean_SourceInfo_fromRef(v_a_387_, v___x_414_);
v___x_448_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_447_, 4);
v___x_449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_451_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_447_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = l_Lean_Syntax_node3(v___x_447_, v___x_450_, v___x_400_, v___x_452_, v___x_446_);
v___x_454_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_447_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_Lean_Syntax_node3(v___x_447_, v___x_402_, v___x_449_, v___x_453_, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_a_388_);
return v___x_457_;
}
}
else
{
uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v___x_413_);
lean_dec(v___x_401_);
v___x_458_ = 0;
v___x_459_ = l_Lean_SourceInfo_fromRef(v_a_387_, v___x_458_);
v___x_460_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_459_, 3);
v___x_461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_463_ = l_Lean_Syntax_node1(v___x_459_, v___x_462_, v___x_400_);
v___x_464_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_459_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Syntax_node3(v___x_459_, v___x_402_, v___x_461_, v___x_463_, v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_a_388_);
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons___boxed(lean_object* v_x_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_Internal_Do_unexpandEPostCons(v_x_468_, v_a_469_, v_a_470_);
lean_dec(v_a_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg(lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_474_ = 0;
v___x_475_ = l_Lean_SourceInfo_fromRef(v_a_472_, v___x_474_);
v___x_476_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
v___x_477_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_475_, 3);
v___x_478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_475_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_480_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_475_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
v___x_482_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_475_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_Syntax_node3(v___x_475_, v___x_476_, v___x_478_, v___x_481_, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_a_473_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg___boxed(lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_486_, v_a_487_);
lean_dec(v_a_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk(lean_object* v_x_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_490_, v_a_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___boxed(lean_object* v_x_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_Internal_Do_unexpandEPostNilMk(v_x_493_, v_a_494_, v_a_495_);
lean_dec(v_a_494_);
lean_dec(v_x_493_);
return v_res_496_;
}
}
static lean_object* _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
v___x_499_ = ((lean_object*)(l_Std_Internal_Do_unexpandEPostCons___closed__1));
v___x_500_ = l_Lean_addMacroScope(v___x_499_, v___x_498_, v___x_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk(lean_object* v_x_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
lean_inc(v_x_501_);
v___x_505_ = l_Lean_Syntax_isOfKind(v_x_501_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_x_501_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_a_503_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = l_Lean_Syntax_getArg(v_x_501_, v___x_508_);
lean_dec(v_x_501_);
v___x_510_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_509_);
v___x_511_ = l_Lean_Syntax_matchesNull(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v_a_503_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = l_Lean_Syntax_getArg(v___x_509_, v___x_514_);
v___x_516_ = l_Lean_Syntax_getArg(v___x_509_, v___x_508_);
lean_dec(v___x_509_);
v___x_517_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
lean_inc(v___x_516_);
v___x_518_ = l_Lean_Syntax_isOfKind(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_519_ = l_Lean_SourceInfo_fromRef(v_a_502_, v___x_518_);
v___x_520_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_521_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostConsMk___closed__0, &l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once, _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0);
v___x_522_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_519_, 2);
v___x_523_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_523_, 0, v___x_519_);
lean_ctor_set(v___x_523_, 1, v___x_520_);
lean_ctor_set(v___x_523_, 2, v___x_521_);
lean_ctor_set(v___x_523_, 3, v___x_522_);
v___x_524_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_525_ = l_Lean_Syntax_node2(v___x_519_, v___x_524_, v___x_515_, v___x_516_);
v___x_526_ = l_Lean_Syntax_node2(v___x_519_, v___x_504_, v___x_523_, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_a_503_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = l_Lean_Syntax_getArg(v___x_516_, v___x_508_);
lean_inc(v___x_528_);
v___x_529_ = l_Lean_Syntax_matchesNull(v___x_528_, v___x_514_);
if (v___x_529_ == 0)
{
uint8_t v___x_530_; 
lean_inc(v___x_528_);
v___x_530_ = l_Lean_Syntax_matchesNull(v___x_528_, v___x_508_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = l_Lean_Syntax_getNumArgs(v___x_528_);
v___x_532_ = lean_nat_dec_le(v___x_510_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v___x_531_);
lean_dec(v___x_528_);
v___x_533_ = l_Lean_SourceInfo_fromRef(v_a_502_, v___x_530_);
v___x_534_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_535_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostConsMk___closed__0, &l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once, _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0);
v___x_536_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_533_, 2);
v___x_537_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_537_, 0, v___x_533_);
lean_ctor_set(v___x_537_, 1, v___x_534_);
lean_ctor_set(v___x_537_, 2, v___x_535_);
lean_ctor_set(v___x_537_, 3, v___x_536_);
v___x_538_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_539_ = l_Lean_Syntax_node2(v___x_533_, v___x_538_, v___x_515_, v___x_516_);
v___x_540_ = l_Lean_Syntax_node2(v___x_533_, v___x_504_, v___x_537_, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v_a_503_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_516_);
v___x_542_ = l_Lean_Syntax_getArg(v___x_528_, v___x_514_);
v___x_543_ = l_Lean_Syntax_getArgs(v___x_528_);
lean_dec(v___x_528_);
v___x_544_ = l_Array_extract___redArg(v___x_543_, v___x_510_, v___x_531_);
lean_dec_ref(v___x_543_);
v___x_545_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_546_ = lean_box(2);
v___x_547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_545_);
lean_ctor_set(v___x_547_, 2, v___x_544_);
v___x_548_ = l_Lean_Syntax_getArgs(v___x_547_);
lean_dec_ref_known(v___x_547_, 3);
v___x_549_ = l_Lean_SourceInfo_fromRef(v_a_502_, v___x_530_);
v___x_550_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_549_, 4);
v___x_551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_549_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
lean_inc_ref(v___x_553_);
v___x_554_ = l_Array_mkArray4___redArg(v___x_515_, v___x_553_, v___x_542_, v___x_553_);
v___x_555_ = l_Array_append___redArg(v___x_554_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_556_, 0, v___x_549_);
lean_ctor_set(v___x_556_, 1, v___x_545_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
v___x_557_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_549_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l_Lean_Syntax_node3(v___x_549_, v___x_517_, v___x_551_, v___x_556_, v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_a_503_);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_516_);
v___x_561_ = l_Lean_Syntax_getArg(v___x_528_, v___x_514_);
lean_dec(v___x_528_);
v___x_562_ = l_Lean_SourceInfo_fromRef(v_a_502_, v___x_529_);
v___x_563_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_562_, 4);
v___x_564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_566_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_562_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_Syntax_node3(v___x_562_, v___x_565_, v___x_515_, v___x_567_, v___x_561_);
v___x_569_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_562_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_Syntax_node3(v___x_562_, v___x_517_, v___x_564_, v___x_568_, v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_a_503_);
return v___x_572_;
}
}
else
{
uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v___x_528_);
lean_dec(v___x_516_);
v___x_573_ = 0;
v___x_574_ = l_Lean_SourceInfo_fromRef(v_a_502_, v___x_573_);
v___x_575_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_574_, 3);
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_578_ = l_Lean_Syntax_node1(v___x_574_, v___x_577_, v___x_515_);
v___x_579_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_574_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = l_Lean_Syntax_node3(v___x_574_, v___x_517_, v___x_576_, v___x_578_, v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v_a_503_);
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk___boxed(lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_Internal_Do_unexpandEPostConsMk(v_x_583_, v_a_584_, v_a_585_);
lean_dec(v_a_584_);
return v_res_586_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_Assertion(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_ExceptPost(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_Do_instPartialOrderNil = _init_l_Std_Internal_Do_instPartialOrderNil();
lean_mark_persistent(l_Std_Internal_Do_instPartialOrderNil);
l_Std_Internal_Do_instCompleteLatticeNil = _init_l_Std_Internal_Do_instCompleteLatticeNil();
lean_mark_persistent(l_Std_Internal_Do_instCompleteLatticeNil);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_ExceptPost(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_Assertion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_ExceptPost(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_ExceptPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_ExceptPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_ExceptPost(builtin);
}
#ifdef __cplusplus
}
#endif
