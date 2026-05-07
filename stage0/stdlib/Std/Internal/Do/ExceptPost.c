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
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_nil_toCtorIdx(lean_object*);
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
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "EPost.cons"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(188, 82, 180, 207, 155, 76, 244, 97)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 34, 106, 80, 62, 31, 229, 248)}};
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
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EPost.nil"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(180, 230, 205, 39, 215, 76, 65, 131)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(66, 168, 39, 204, 144, 61, 226, 28)}};
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
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "EPost.cons.mk"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(188, 82, 180, 207, 155, 76, 244, 97)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 36, 136, 213, 243, 244, 168, 122)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 34, 106, 80, 62, 31, 229, 248)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_4),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 6, 98, 206, 152, 24, 169, 121)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "EPost.nil.mk"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 238, 175, 188, 148, 170, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(180, 230, 205, 39, 215, 76, 65, 131)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(28, 173, 12, 145, 216, 25, 125, 160)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_0),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_1),((lean_object*)&l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_3),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(66, 168, 39, 204, 144, 61, 226, 28)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_4),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(98, 241, 255, 45, 198, 76, 108, 146)}};
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
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_nil_toCtorIdx(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Internal_Do_instPartialOrderNil(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Internal_Do_instCompleteLatticeNil(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instPartialOrderCons(lean_object* v_eh_5_, lean_object* v_et_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instCompleteLatticeCons(lean_object* v_eh_10_, lean_object* v_et_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7));
v___x_97_ = l_String_toRawSubstring_x27(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Array_mkArray0(lean_box(0));
return v___x_120_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18));
v___x_123_ = l_String_toRawSubstring_x27(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(lean_object* v_x_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
lean_inc(v_x_145_);
v___x_149_ = l_Lean_Syntax_isOfKind(v_x_145_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_x_145_);
v___x_150_ = lean_box(1);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_147_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_145_, v___x_153_);
lean_dec(v_x_145_);
lean_inc(v___x_154_);
v___x_155_ = l_Lean_Syntax_matchesNull(v___x_154_, v___x_152_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
lean_inc(v___x_154_);
v___x_156_ = l_Lean_Syntax_matchesNull(v___x_154_, v___x_153_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = l_Lean_Syntax_getNumArgs(v___x_154_);
v___x_159_ = lean_nat_dec_le(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v___x_158_);
lean_dec(v___x_154_);
v___x_160_ = lean_box(1);
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_a_147_);
return v___x_161_;
}
else
{
lean_object* v_quotContext_162_; lean_object* v_currMacroScope_163_; lean_object* v_ref_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_quotContext_162_ = lean_ctor_get(v_a_146_, 1);
v_currMacroScope_163_ = lean_ctor_get(v_a_146_, 2);
v_ref_164_ = lean_ctor_get(v_a_146_, 5);
v___x_165_ = l_Lean_Syntax_getArg(v___x_154_, v___x_152_);
v___x_166_ = l_Lean_Syntax_getArgs(v___x_154_);
lean_dec(v___x_154_);
v___x_167_ = l_Array_extract___redArg(v___x_166_, v___x_157_, v___x_158_);
lean_dec_ref(v___x_166_);
v___x_168_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_169_ = lean_box(2);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
v___x_171_ = l_Lean_Syntax_getArgs(v___x_170_);
lean_dec_ref(v___x_170_);
v___x_172_ = l_Lean_SourceInfo_fromRef(v_ref_164_, v___x_156_);
v___x_173_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_174_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_175_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
lean_inc(v_currMacroScope_163_);
lean_inc(v_quotContext_162_);
v___x_176_ = l_Lean_addMacroScope(v_quotContext_162_, v___x_175_, v_currMacroScope_163_);
v___x_177_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_172_, 6);
v___x_178_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_178_, 0, v___x_172_);
lean_ctor_set(v___x_178_, 1, v___x_174_);
lean_ctor_set(v___x_178_, 2, v___x_176_);
lean_ctor_set(v___x_178_, 3, v___x_177_);
v___x_179_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
v___x_180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_172_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_182_ = l_Array_append___redArg(v___x_181_, v___x_171_);
lean_dec_ref(v___x_171_);
v___x_183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_183_, 0, v___x_172_);
lean_ctor_set(v___x_183_, 1, v___x_168_);
lean_ctor_set(v___x_183_, 2, v___x_182_);
v___x_184_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_172_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = l_Lean_Syntax_node3(v___x_172_, v___x_148_, v___x_180_, v___x_183_, v___x_185_);
v___x_187_ = l_Lean_Syntax_node2(v___x_172_, v___x_168_, v___x_165_, v___x_186_);
v___x_188_ = l_Lean_Syntax_node2(v___x_172_, v___x_173_, v___x_178_, v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_147_);
return v___x_189_;
}
}
else
{
lean_object* v_quotContext_190_; lean_object* v_currMacroScope_191_; lean_object* v_ref_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_quotContext_190_ = lean_ctor_get(v_a_146_, 1);
v_currMacroScope_191_ = lean_ctor_get(v_a_146_, 2);
v_ref_192_ = lean_ctor_get(v_a_146_, 5);
v___x_193_ = l_Lean_Syntax_getArg(v___x_154_, v___x_152_);
lean_dec(v___x_154_);
v___x_194_ = l_Lean_SourceInfo_fromRef(v_ref_192_, v___x_155_);
v___x_195_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_196_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_197_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
lean_inc_n(v_currMacroScope_191_, 2);
lean_inc_n(v_quotContext_190_, 2);
v___x_198_ = l_Lean_addMacroScope(v_quotContext_190_, v___x_197_, v_currMacroScope_191_);
v___x_199_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_194_, 3);
v___x_200_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_200_, 0, v___x_194_);
lean_ctor_set(v___x_200_, 1, v___x_196_);
lean_ctor_set(v___x_200_, 2, v___x_198_);
lean_ctor_set(v___x_200_, 3, v___x_199_);
v___x_201_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_202_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
v___x_203_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21));
v___x_204_ = l_Lean_addMacroScope(v_quotContext_190_, v___x_203_, v_currMacroScope_191_);
v___x_205_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26));
v___x_206_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_206_, 0, v___x_194_);
lean_ctor_set(v___x_206_, 1, v___x_202_);
lean_ctor_set(v___x_206_, 2, v___x_204_);
lean_ctor_set(v___x_206_, 3, v___x_205_);
v___x_207_ = l_Lean_Syntax_node2(v___x_194_, v___x_201_, v___x_193_, v___x_206_);
v___x_208_ = l_Lean_Syntax_node2(v___x_194_, v___x_195_, v___x_200_, v___x_207_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v_a_147_);
return v___x_209_;
}
}
else
{
lean_object* v_quotContext_210_; lean_object* v_currMacroScope_211_; lean_object* v_ref_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___x_154_);
v_quotContext_210_ = lean_ctor_get(v_a_146_, 1);
v_currMacroScope_211_ = lean_ctor_get(v_a_146_, 2);
v_ref_212_ = lean_ctor_get(v_a_146_, 5);
v___x_213_ = 0;
v___x_214_ = l_Lean_SourceInfo_fromRef(v_ref_212_, v___x_213_);
v___x_215_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
v___x_216_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21));
lean_inc(v_currMacroScope_211_);
lean_inc(v_quotContext_210_);
v___x_217_ = l_Lean_addMacroScope(v_quotContext_210_, v___x_216_, v_currMacroScope_211_);
v___x_218_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26));
v___x_219_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_219_, 0, v___x_214_);
lean_ctor_set(v___x_219_, 1, v___x_215_);
lean_ctor_set(v___x_219_, 2, v___x_217_);
lean_ctor_set(v___x_219_, 3, v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_a_147_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___boxed(lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(v_x_221_, v_a_222_, v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_224_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0));
v___x_227_ = l_String_toRawSubstring_x27(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9));
v___x_253_ = l_String_toRawSubstring_x27(v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(lean_object* v_x_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
lean_inc(v_x_276_);
v___x_280_ = l_Lean_Syntax_isOfKind(v_x_276_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_x_276_);
v___x_281_ = lean_box(1);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_a_278_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = l_Lean_Syntax_getArg(v_x_276_, v___x_284_);
lean_dec(v_x_276_);
lean_inc(v___x_285_);
v___x_286_ = l_Lean_Syntax_matchesNull(v___x_285_, v___x_283_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
lean_inc(v___x_285_);
v___x_287_ = l_Lean_Syntax_matchesNull(v___x_285_, v___x_284_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(2u);
v___x_289_ = l_Lean_Syntax_getNumArgs(v___x_285_);
v___x_290_ = lean_nat_dec_le(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v___x_289_);
lean_dec(v___x_285_);
v___x_291_ = lean_box(1);
v___x_292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_a_278_);
return v___x_292_;
}
else
{
lean_object* v_quotContext_293_; lean_object* v_currMacroScope_294_; lean_object* v_ref_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_quotContext_293_ = lean_ctor_get(v_a_277_, 1);
v_currMacroScope_294_ = lean_ctor_get(v_a_277_, 2);
v_ref_295_ = lean_ctor_get(v_a_277_, 5);
v___x_296_ = l_Lean_Syntax_getArg(v___x_285_, v___x_283_);
v___x_297_ = l_Lean_Syntax_getArgs(v___x_285_);
lean_dec(v___x_285_);
v___x_298_ = l_Array_extract___redArg(v___x_297_, v___x_288_, v___x_289_);
lean_dec_ref(v___x_297_);
v___x_299_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_300_ = lean_box(2);
v___x_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
lean_ctor_set(v___x_301_, 2, v___x_298_);
v___x_302_ = l_Lean_Syntax_getArgs(v___x_301_);
lean_dec_ref(v___x_301_);
v___x_303_ = l_Lean_SourceInfo_fromRef(v_ref_295_, v___x_287_);
v___x_304_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_305_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_306_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
lean_inc(v_currMacroScope_294_);
lean_inc(v_quotContext_293_);
v___x_307_ = l_Lean_addMacroScope(v_quotContext_293_, v___x_306_, v_currMacroScope_294_);
v___x_308_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_303_, 6);
v___x_309_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_309_, 0, v___x_303_);
lean_ctor_set(v___x_309_, 1, v___x_305_);
lean_ctor_set(v___x_309_, 2, v___x_307_);
lean_ctor_set(v___x_309_, 3, v___x_308_);
v___x_310_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
v___x_311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_303_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_313_ = l_Array_append___redArg(v___x_312_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v___x_303_);
lean_ctor_set(v___x_314_, 1, v___x_299_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
v___x_315_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_303_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_Syntax_node3(v___x_303_, v___x_279_, v___x_311_, v___x_314_, v___x_316_);
v___x_318_ = l_Lean_Syntax_node2(v___x_303_, v___x_299_, v___x_296_, v___x_317_);
v___x_319_ = l_Lean_Syntax_node2(v___x_303_, v___x_304_, v___x_309_, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_278_);
return v___x_320_;
}
}
else
{
lean_object* v_quotContext_321_; lean_object* v_currMacroScope_322_; lean_object* v_ref_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_quotContext_321_ = lean_ctor_get(v_a_277_, 1);
v_currMacroScope_322_ = lean_ctor_get(v_a_277_, 2);
v_ref_323_ = lean_ctor_get(v_a_277_, 5);
v___x_324_ = l_Lean_Syntax_getArg(v___x_285_, v___x_283_);
lean_dec(v___x_285_);
v___x_325_ = l_Lean_SourceInfo_fromRef(v_ref_323_, v___x_286_);
v___x_326_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_327_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_328_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
lean_inc_n(v_currMacroScope_322_, 2);
lean_inc_n(v_quotContext_321_, 2);
v___x_329_ = l_Lean_addMacroScope(v_quotContext_321_, v___x_328_, v_currMacroScope_322_);
v___x_330_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_325_, 3);
v___x_331_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_331_, 0, v___x_325_);
lean_ctor_set(v___x_331_, 1, v___x_327_);
lean_ctor_set(v___x_331_, 2, v___x_329_);
lean_ctor_set(v___x_331_, 3, v___x_330_);
v___x_332_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_333_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
v___x_334_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11));
v___x_335_ = l_Lean_addMacroScope(v_quotContext_321_, v___x_334_, v_currMacroScope_322_);
v___x_336_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16));
v___x_337_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_337_, 0, v___x_325_);
lean_ctor_set(v___x_337_, 1, v___x_333_);
lean_ctor_set(v___x_337_, 2, v___x_335_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
v___x_338_ = l_Lean_Syntax_node2(v___x_325_, v___x_332_, v___x_324_, v___x_337_);
v___x_339_ = l_Lean_Syntax_node2(v___x_325_, v___x_326_, v___x_331_, v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_a_278_);
return v___x_340_;
}
}
else
{
lean_object* v_quotContext_341_; lean_object* v_currMacroScope_342_; lean_object* v_ref_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v___x_285_);
v_quotContext_341_ = lean_ctor_get(v_a_277_, 1);
v_currMacroScope_342_ = lean_ctor_get(v_a_277_, 2);
v_ref_343_ = lean_ctor_get(v_a_277_, 5);
v___x_344_ = 0;
v___x_345_ = l_Lean_SourceInfo_fromRef(v_ref_343_, v___x_344_);
v___x_346_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
v___x_347_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11));
lean_inc(v_currMacroScope_342_);
lean_inc(v_quotContext_341_);
v___x_348_ = l_Lean_addMacroScope(v_quotContext_341_, v___x_347_, v_currMacroScope_342_);
v___x_349_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16));
v___x_350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_350_, 0, v___x_345_);
lean_ctor_set(v___x_350_, 1, v___x_346_);
lean_ctor_set(v___x_350_, 2, v___x_348_);
lean_ctor_set(v___x_350_, 3, v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_a_278_);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___boxed(lean_object* v_x_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(v_x_352_, v_a_353_, v_a_354_);
lean_dec_ref(v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg(lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_358_ = 0;
v___x_359_ = l_Lean_SourceInfo_fromRef(v_a_356_, v___x_358_);
v___x_360_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
v___x_361_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_359_, 3);
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_359_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_364_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_365_, 0, v___x_359_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_364_);
v___x_366_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_359_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = l_Lean_Syntax_node3(v___x_359_, v___x_360_, v___x_362_, v___x_365_, v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_a_357_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg___boxed(lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_370_, v_a_371_);
lean_dec(v_a_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil(lean_object* v_x_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_374_, v_a_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___boxed(lean_object* v_x_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Internal_Do_unexpandEPostNil(v_x_377_, v_a_378_, v_a_379_);
lean_dec(v_a_378_);
lean_dec(v_x_377_);
return v_res_380_;
}
}
static lean_object* _init_l_Std_Internal_Do_unexpandEPostCons___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
v___x_386_ = ((lean_object*)(l_Std_Internal_Do_unexpandEPostCons___closed__1));
v___x_387_ = l_Lean_addMacroScope(v___x_386_, v___x_385_, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons(lean_object* v_x_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
lean_inc(v_x_388_);
v___x_392_ = l_Lean_Syntax_isOfKind(v_x_388_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_x_388_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_a_390_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = l_Lean_Syntax_getArg(v_x_388_, v___x_395_);
lean_dec(v_x_388_);
v___x_397_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_396_);
v___x_398_ = l_Lean_Syntax_matchesNull(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_a_390_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = l_Lean_Syntax_getArg(v___x_396_, v___x_401_);
v___x_403_ = l_Lean_Syntax_getArg(v___x_396_, v___x_395_);
lean_dec(v___x_396_);
v___x_404_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
lean_inc(v___x_403_);
v___x_405_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_406_ = l_Lean_SourceInfo_fromRef(v_a_389_, v___x_405_);
v___x_407_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_408_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostCons___closed__2, &l_Std_Internal_Do_unexpandEPostCons___closed__2_once, _init_l_Std_Internal_Do_unexpandEPostCons___closed__2);
v___x_409_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_406_, 2);
v___x_410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_410_, 0, v___x_406_);
lean_ctor_set(v___x_410_, 1, v___x_407_);
lean_ctor_set(v___x_410_, 2, v___x_408_);
lean_ctor_set(v___x_410_, 3, v___x_409_);
v___x_411_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_412_ = l_Lean_Syntax_node2(v___x_406_, v___x_411_, v___x_402_, v___x_403_);
v___x_413_ = l_Lean_Syntax_node2(v___x_406_, v___x_391_, v___x_410_, v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v_a_390_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = l_Lean_Syntax_getArg(v___x_403_, v___x_395_);
lean_inc(v___x_415_);
v___x_416_ = l_Lean_Syntax_matchesNull(v___x_415_, v___x_401_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
lean_inc(v___x_415_);
v___x_417_ = l_Lean_Syntax_matchesNull(v___x_415_, v___x_395_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = l_Lean_Syntax_getNumArgs(v___x_415_);
v___x_419_ = lean_nat_dec_le(v___x_397_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v___x_418_);
lean_dec(v___x_415_);
v___x_420_ = l_Lean_SourceInfo_fromRef(v_a_389_, v___x_417_);
v___x_421_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_422_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostCons___closed__2, &l_Std_Internal_Do_unexpandEPostCons___closed__2_once, _init_l_Std_Internal_Do_unexpandEPostCons___closed__2);
v___x_423_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_420_, 2);
v___x_424_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_424_, 0, v___x_420_);
lean_ctor_set(v___x_424_, 1, v___x_421_);
lean_ctor_set(v___x_424_, 2, v___x_422_);
lean_ctor_set(v___x_424_, 3, v___x_423_);
v___x_425_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_426_ = l_Lean_Syntax_node2(v___x_420_, v___x_425_, v___x_402_, v___x_403_);
v___x_427_ = l_Lean_Syntax_node2(v___x_420_, v___x_391_, v___x_424_, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_a_390_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v___x_403_);
v___x_429_ = l_Lean_Syntax_getArg(v___x_415_, v___x_401_);
v___x_430_ = l_Lean_Syntax_getArgs(v___x_415_);
lean_dec(v___x_415_);
v___x_431_ = l_Array_extract___redArg(v___x_430_, v___x_397_, v___x_418_);
lean_dec_ref(v___x_430_);
v___x_432_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_433_ = lean_box(2);
v___x_434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_431_);
v___x_435_ = l_Lean_Syntax_getArgs(v___x_434_);
lean_dec_ref(v___x_434_);
v___x_436_ = l_Lean_SourceInfo_fromRef(v_a_389_, v___x_417_);
v___x_437_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_436_, 4);
v___x_438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_436_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
lean_inc_ref(v___x_440_);
v___x_441_ = l_Array_mkArray4___redArg(v___x_402_, v___x_440_, v___x_429_, v___x_440_);
v___x_442_ = l_Array_append___redArg(v___x_441_, v___x_435_);
lean_dec_ref(v___x_435_);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v___x_436_);
lean_ctor_set(v___x_443_, 1, v___x_432_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
v___x_444_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_436_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_Syntax_node3(v___x_436_, v___x_404_, v___x_438_, v___x_443_, v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v_a_390_);
return v___x_447_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_403_);
v___x_448_ = l_Lean_Syntax_getArg(v___x_415_, v___x_401_);
lean_dec(v___x_415_);
v___x_449_ = l_Lean_SourceInfo_fromRef(v_a_389_, v___x_416_);
v___x_450_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_449_, 4);
v___x_451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_453_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_449_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_Syntax_node3(v___x_449_, v___x_452_, v___x_402_, v___x_454_, v___x_448_);
v___x_456_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_449_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_Syntax_node3(v___x_449_, v___x_404_, v___x_451_, v___x_455_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_a_390_);
return v___x_459_;
}
}
else
{
uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v___x_415_);
lean_dec(v___x_403_);
v___x_460_ = 0;
v___x_461_ = l_Lean_SourceInfo_fromRef(v_a_389_, v___x_460_);
v___x_462_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_461_, 3);
v___x_463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_465_ = l_Lean_Syntax_node1(v___x_461_, v___x_464_, v___x_402_);
v___x_466_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_461_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_Syntax_node3(v___x_461_, v___x_404_, v___x_463_, v___x_465_, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_a_390_);
return v___x_469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons___boxed(lean_object* v_x_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_Internal_Do_unexpandEPostCons(v_x_470_, v_a_471_, v_a_472_);
lean_dec(v_a_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg(lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_476_ = 0;
v___x_477_ = l_Lean_SourceInfo_fromRef(v_a_474_, v___x_476_);
v___x_478_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
v___x_479_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_477_, 3);
v___x_480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_477_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_482_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_483_, 0, v___x_477_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
v___x_484_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_477_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_Syntax_node3(v___x_477_, v___x_478_, v___x_480_, v___x_483_, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_a_475_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg___boxed(lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_488_, v_a_489_);
lean_dec(v_a_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk(lean_object* v_x_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_492_, v_a_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___boxed(lean_object* v_x_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Internal_Do_unexpandEPostNilMk(v_x_495_, v_a_496_, v_a_497_);
lean_dec(v_a_496_);
lean_dec(v_x_495_);
return v_res_498_;
}
}
static lean_object* _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
v___x_501_ = ((lean_object*)(l_Std_Internal_Do_unexpandEPostCons___closed__1));
v___x_502_ = l_Lean_addMacroScope(v___x_501_, v___x_500_, v___x_499_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk(lean_object* v_x_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
lean_inc(v_x_503_);
v___x_507_ = l_Lean_Syntax_isOfKind(v_x_503_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_x_503_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_505_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = l_Lean_Syntax_getArg(v_x_503_, v___x_510_);
lean_dec(v_x_503_);
v___x_512_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_511_);
v___x_513_ = l_Lean_Syntax_matchesNull(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_a_505_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Lean_Syntax_getArg(v___x_511_, v___x_516_);
v___x_518_ = l_Lean_Syntax_getArg(v___x_511_, v___x_510_);
lean_dec(v___x_511_);
v___x_519_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
lean_inc(v___x_518_);
v___x_520_ = l_Lean_Syntax_isOfKind(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_521_ = l_Lean_SourceInfo_fromRef(v_a_504_, v___x_520_);
v___x_522_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_523_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostConsMk___closed__0, &l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once, _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0);
v___x_524_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_521_, 2);
v___x_525_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_525_, 0, v___x_521_);
lean_ctor_set(v___x_525_, 1, v___x_522_);
lean_ctor_set(v___x_525_, 2, v___x_523_);
lean_ctor_set(v___x_525_, 3, v___x_524_);
v___x_526_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_527_ = l_Lean_Syntax_node2(v___x_521_, v___x_526_, v___x_517_, v___x_518_);
v___x_528_ = l_Lean_Syntax_node2(v___x_521_, v___x_506_, v___x_525_, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_a_505_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = l_Lean_Syntax_getArg(v___x_518_, v___x_510_);
lean_inc(v___x_530_);
v___x_531_ = l_Lean_Syntax_matchesNull(v___x_530_, v___x_516_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
lean_inc(v___x_530_);
v___x_532_ = l_Lean_Syntax_matchesNull(v___x_530_, v___x_510_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = l_Lean_Syntax_getNumArgs(v___x_530_);
v___x_534_ = lean_nat_dec_le(v___x_512_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v___x_533_);
lean_dec(v___x_530_);
v___x_535_ = l_Lean_SourceInfo_fromRef(v_a_504_, v___x_532_);
v___x_536_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_537_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostConsMk___closed__0, &l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once, _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0);
v___x_538_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_535_, 2);
v___x_539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_539_, 0, v___x_535_);
lean_ctor_set(v___x_539_, 1, v___x_536_);
lean_ctor_set(v___x_539_, 2, v___x_537_);
lean_ctor_set(v___x_539_, 3, v___x_538_);
v___x_540_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_541_ = l_Lean_Syntax_node2(v___x_535_, v___x_540_, v___x_517_, v___x_518_);
v___x_542_ = l_Lean_Syntax_node2(v___x_535_, v___x_506_, v___x_539_, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_a_505_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_518_);
v___x_544_ = l_Lean_Syntax_getArg(v___x_530_, v___x_516_);
v___x_545_ = l_Lean_Syntax_getArgs(v___x_530_);
lean_dec(v___x_530_);
v___x_546_ = l_Array_extract___redArg(v___x_545_, v___x_512_, v___x_533_);
lean_dec_ref(v___x_545_);
v___x_547_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_548_ = lean_box(2);
v___x_549_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_547_);
lean_ctor_set(v___x_549_, 2, v___x_546_);
v___x_550_ = l_Lean_Syntax_getArgs(v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = l_Lean_SourceInfo_fromRef(v_a_504_, v___x_532_);
v___x_552_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_551_, 4);
v___x_553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
lean_inc_ref(v___x_555_);
v___x_556_ = l_Array_mkArray4___redArg(v___x_517_, v___x_555_, v___x_544_, v___x_555_);
v___x_557_ = l_Array_append___redArg(v___x_556_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_558_, 0, v___x_551_);
lean_ctor_set(v___x_558_, 1, v___x_547_);
lean_ctor_set(v___x_558_, 2, v___x_557_);
v___x_559_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_551_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_Syntax_node3(v___x_551_, v___x_519_, v___x_553_, v___x_558_, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_a_505_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_518_);
v___x_563_ = l_Lean_Syntax_getArg(v___x_530_, v___x_516_);
lean_dec(v___x_530_);
v___x_564_ = l_Lean_SourceInfo_fromRef(v_a_504_, v___x_531_);
v___x_565_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_564_, 4);
v___x_566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_568_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_564_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Lean_Syntax_node3(v___x_564_, v___x_567_, v___x_517_, v___x_569_, v___x_563_);
v___x_571_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_564_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_Syntax_node3(v___x_564_, v___x_519_, v___x_566_, v___x_570_, v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v_a_505_);
return v___x_574_;
}
}
else
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v___x_530_);
lean_dec(v___x_518_);
v___x_575_ = 0;
v___x_576_ = l_Lean_SourceInfo_fromRef(v_a_504_, v___x_575_);
v___x_577_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_576_, 3);
v___x_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_580_ = l_Lean_Syntax_node1(v___x_576_, v___x_579_, v___x_517_);
v___x_581_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_576_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_Syntax_node3(v___x_576_, v___x_519_, v___x_578_, v___x_580_, v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_a_505_);
return v___x_584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk___boxed(lean_object* v_x_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_Internal_Do_unexpandEPostConsMk(v_x_585_, v_a_586_, v_a_587_);
lean_dec(v_a_586_);
return v_res_588_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_Assertion(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_ExceptPost(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
