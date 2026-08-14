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
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushExcept___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushExcept___redArg(lean_object* v_post_1_, lean_object* v_epost_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v_a_4_; lean_object* v_head_5_; lean_object* v___x_6_; 
lean_dec(v_post_1_);
v_a_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_3_, 1);
v_head_5_ = lean_ctor_get(v_epost_2_, 0);
lean_inc(v_head_5_);
lean_dec_ref(v_epost_2_);
v___x_6_ = lean_apply_1(v_head_5_, v_a_4_);
return v___x_6_;
}
else
{
lean_object* v_a_7_; lean_object* v___x_8_; 
lean_dec_ref(v_epost_2_);
v_a_7_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_a_7_);
lean_dec_ref_known(v_x_3_, 1);
v___x_8_ = lean_apply_1(v_post_1_, v_a_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushExcept(lean_object* v_00_u03b1_9_, lean_object* v_00_u03b5_10_, lean_object* v_Pred_11_, lean_object* v_EPred_12_, lean_object* v_post_13_, lean_object* v_epost_14_, lean_object* v_x_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Std_Internal_Do_EPost_Cons_pushExcept___redArg(v_post_13_, v_epost_14_, v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption___redArg(lean_object* v_post_17_, lean_object* v_epost_18_, lean_object* v_x_19_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
lean_object* v_head_20_; 
lean_dec(v_post_17_);
v_head_20_ = lean_ctor_get(v_epost_18_, 0);
lean_inc(v_head_20_);
return v_head_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_22_; 
v_val_21_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v_x_19_, 1);
v___x_22_ = lean_apply_1(v_post_17_, v_val_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption___redArg___boxed(lean_object* v_post_23_, lean_object* v_epost_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Internal_Do_EPost_Cons_pushOption___redArg(v_post_23_, v_epost_24_, v_x_25_);
lean_dec_ref(v_epost_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption(lean_object* v_00_u03b1_27_, lean_object* v_Pred_28_, lean_object* v_EPred_29_, lean_object* v_post_30_, lean_object* v_epost_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Internal_Do_EPost_Cons_pushOption___redArg(v_post_30_, v_epost_31_, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_EPost_Cons_pushOption___boxed(lean_object* v_00_u03b1_34_, lean_object* v_Pred_35_, lean_object* v_EPred_36_, lean_object* v_post_37_, lean_object* v_epost_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Internal_Do_EPost_Cons_pushOption(v_00_u03b1_34_, v_Pred_35_, v_EPred_36_, v_post_37_, v_epost_38_, v_x_39_);
lean_dec_ref(v_epost_38_);
return v_res_40_;
}
}
static lean_object* _init_l_Std_Internal_Do_instPartialOrderNil(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_box(0);
return v___x_41_;
}
}
static lean_object* _init_l_Std_Internal_Do_instCompleteLatticeNil(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instPartialOrderCons(lean_object* v_eh_43_, lean_object* v_et_44_, lean_object* v_inst_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instCompleteLatticeCons(lean_object* v_eh_48_, lean_object* v_et_49_, lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7));
v___x_135_ = l_String_toRawSubstring_x27(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Array_mkArray0(lean_box(0));
return v___x_158_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18));
v___x_161_ = l_String_toRawSubstring_x27(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(lean_object* v_x_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
lean_inc(v_x_183_);
v___x_187_ = l_Lean_Syntax_isOfKind(v_x_183_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_x_183_);
v___x_188_ = lean_box(1);
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = l_Lean_Syntax_getArg(v_x_183_, v___x_191_);
lean_dec(v_x_183_);
lean_inc(v___x_192_);
v___x_193_ = l_Lean_Syntax_matchesNull(v___x_192_, v___x_190_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
lean_inc(v___x_192_);
v___x_194_ = l_Lean_Syntax_matchesNull(v___x_192_, v___x_191_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = l_Lean_Syntax_getNumArgs(v___x_192_);
v___x_197_ = lean_nat_dec_le(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v___x_196_);
lean_dec(v___x_192_);
v___x_198_ = lean_box(1);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_185_);
return v___x_199_;
}
else
{
lean_object* v_quotContext_200_; lean_object* v_currMacroScope_201_; lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_quotContext_200_ = lean_ctor_get(v_a_184_, 1);
v_currMacroScope_201_ = lean_ctor_get(v_a_184_, 2);
v_ref_202_ = lean_ctor_get(v_a_184_, 5);
v___x_203_ = l_Lean_Syntax_getArg(v___x_192_, v___x_190_);
v___x_204_ = l_Lean_Syntax_getArgs(v___x_192_);
lean_dec(v___x_192_);
v___x_205_ = l_Array_extract___redArg(v___x_204_, v___x_195_, v___x_196_);
lean_dec_ref(v___x_204_);
v___x_206_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_207_ = lean_box(2);
v___x_208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
lean_ctor_set(v___x_208_, 2, v___x_205_);
v___x_209_ = l_Lean_Syntax_getArgs(v___x_208_);
lean_dec_ref_known(v___x_208_, 3);
v___x_210_ = l_Lean_SourceInfo_fromRef(v_ref_202_, v___x_194_);
v___x_211_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_212_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_213_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
lean_inc(v_currMacroScope_201_);
lean_inc(v_quotContext_200_);
v___x_214_ = l_Lean_addMacroScope(v_quotContext_200_, v___x_213_, v_currMacroScope_201_);
v___x_215_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_210_, 6);
v___x_216_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_216_, 0, v___x_210_);
lean_ctor_set(v___x_216_, 1, v___x_212_);
lean_ctor_set(v___x_216_, 2, v___x_214_);
lean_ctor_set(v___x_216_, 3, v___x_215_);
v___x_217_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_210_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_220_ = l_Array_append___redArg(v___x_219_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_221_, 0, v___x_210_);
lean_ctor_set(v___x_221_, 1, v___x_206_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
v___x_222_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_210_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_Syntax_node3(v___x_210_, v___x_186_, v___x_218_, v___x_221_, v___x_223_);
v___x_225_ = l_Lean_Syntax_node2(v___x_210_, v___x_206_, v___x_203_, v___x_224_);
v___x_226_ = l_Lean_Syntax_node2(v___x_210_, v___x_211_, v___x_216_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_185_);
return v___x_227_;
}
}
else
{
lean_object* v_quotContext_228_; lean_object* v_currMacroScope_229_; lean_object* v_ref_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_quotContext_228_ = lean_ctor_get(v_a_184_, 1);
v_currMacroScope_229_ = lean_ctor_get(v_a_184_, 2);
v_ref_230_ = lean_ctor_get(v_a_184_, 5);
v___x_231_ = l_Lean_Syntax_getArg(v___x_192_, v___x_190_);
lean_dec(v___x_192_);
v___x_232_ = l_Lean_SourceInfo_fromRef(v_ref_230_, v___x_193_);
v___x_233_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_234_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_235_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
lean_inc_n(v_currMacroScope_229_, 2);
lean_inc_n(v_quotContext_228_, 2);
v___x_236_ = l_Lean_addMacroScope(v_quotContext_228_, v___x_235_, v_currMacroScope_229_);
v___x_237_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_232_, 3);
v___x_238_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_238_, 0, v___x_232_);
lean_ctor_set(v___x_238_, 1, v___x_234_);
lean_ctor_set(v___x_238_, 2, v___x_236_);
lean_ctor_set(v___x_238_, 3, v___x_237_);
v___x_239_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_240_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
v___x_241_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21));
v___x_242_ = l_Lean_addMacroScope(v_quotContext_228_, v___x_241_, v_currMacroScope_229_);
v___x_243_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26));
v___x_244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_244_, 0, v___x_232_);
lean_ctor_set(v___x_244_, 1, v___x_240_);
lean_ctor_set(v___x_244_, 2, v___x_242_);
lean_ctor_set(v___x_244_, 3, v___x_243_);
v___x_245_ = l_Lean_Syntax_node2(v___x_232_, v___x_239_, v___x_231_, v___x_244_);
v___x_246_ = l_Lean_Syntax_node2(v___x_232_, v___x_233_, v___x_238_, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_185_);
return v___x_247_;
}
}
else
{
lean_object* v_quotContext_248_; lean_object* v_currMacroScope_249_; lean_object* v_ref_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___x_192_);
v_quotContext_248_ = lean_ctor_get(v_a_184_, 1);
v_currMacroScope_249_ = lean_ctor_get(v_a_184_, 2);
v_ref_250_ = lean_ctor_get(v_a_184_, 5);
v___x_251_ = 0;
v___x_252_ = l_Lean_SourceInfo_fromRef(v_ref_250_, v___x_251_);
v___x_253_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
v___x_254_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21));
lean_inc(v_currMacroScope_249_);
lean_inc(v_quotContext_248_);
v___x_255_ = l_Lean_addMacroScope(v_quotContext_248_, v___x_254_, v_currMacroScope_249_);
v___x_256_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26));
v___x_257_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_257_, 0, v___x_252_);
lean_ctor_set(v___x_257_, 1, v___x_253_);
lean_ctor_set(v___x_257_, 2, v___x_255_);
lean_ctor_set(v___x_257_, 3, v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_a_185_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___boxed(lean_object* v_x_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(v_x_259_, v_a_260_, v_a_261_);
lean_dec_ref(v_a_260_);
return v_res_262_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0));
v___x_265_ = l_String_toRawSubstring_x27(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9));
v___x_291_ = l_String_toRawSubstring_x27(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(lean_object* v_x_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
lean_inc(v_x_314_);
v___x_318_ = l_Lean_Syntax_isOfKind(v_x_314_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_x_314_);
v___x_319_ = lean_box(1);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_316_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = l_Lean_Syntax_getArg(v_x_314_, v___x_322_);
lean_dec(v_x_314_);
lean_inc(v___x_323_);
v___x_324_ = l_Lean_Syntax_matchesNull(v___x_323_, v___x_321_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
lean_inc(v___x_323_);
v___x_325_ = l_Lean_Syntax_matchesNull(v___x_323_, v___x_322_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(2u);
v___x_327_ = l_Lean_Syntax_getNumArgs(v___x_323_);
v___x_328_ = lean_nat_dec_le(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v___x_327_);
lean_dec(v___x_323_);
v___x_329_ = lean_box(1);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_a_316_);
return v___x_330_;
}
else
{
lean_object* v_quotContext_331_; lean_object* v_currMacroScope_332_; lean_object* v_ref_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_quotContext_331_ = lean_ctor_get(v_a_315_, 1);
v_currMacroScope_332_ = lean_ctor_get(v_a_315_, 2);
v_ref_333_ = lean_ctor_get(v_a_315_, 5);
v___x_334_ = l_Lean_Syntax_getArg(v___x_323_, v___x_321_);
v___x_335_ = l_Lean_Syntax_getArgs(v___x_323_);
lean_dec(v___x_323_);
v___x_336_ = l_Array_extract___redArg(v___x_335_, v___x_326_, v___x_327_);
lean_dec_ref(v___x_335_);
v___x_337_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_338_ = lean_box(2);
v___x_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
lean_ctor_set(v___x_339_, 2, v___x_336_);
v___x_340_ = l_Lean_Syntax_getArgs(v___x_339_);
lean_dec_ref_known(v___x_339_, 3);
v___x_341_ = l_Lean_SourceInfo_fromRef(v_ref_333_, v___x_325_);
v___x_342_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_343_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_344_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
lean_inc(v_currMacroScope_332_);
lean_inc(v_quotContext_331_);
v___x_345_ = l_Lean_addMacroScope(v_quotContext_331_, v___x_344_, v_currMacroScope_332_);
v___x_346_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_341_, 6);
v___x_347_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_347_, 0, v___x_341_);
lean_ctor_set(v___x_347_, 1, v___x_343_);
lean_ctor_set(v___x_347_, 2, v___x_345_);
lean_ctor_set(v___x_347_, 3, v___x_346_);
v___x_348_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_341_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_351_ = l_Array_append___redArg(v___x_350_, v___x_340_);
lean_dec_ref(v___x_340_);
v___x_352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_352_, 0, v___x_341_);
lean_ctor_set(v___x_352_, 1, v___x_337_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
v___x_353_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_341_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = l_Lean_Syntax_node3(v___x_341_, v___x_317_, v___x_349_, v___x_352_, v___x_354_);
v___x_356_ = l_Lean_Syntax_node2(v___x_341_, v___x_337_, v___x_334_, v___x_355_);
v___x_357_ = l_Lean_Syntax_node2(v___x_341_, v___x_342_, v___x_347_, v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_a_316_);
return v___x_358_;
}
}
else
{
lean_object* v_quotContext_359_; lean_object* v_currMacroScope_360_; lean_object* v_ref_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_quotContext_359_ = lean_ctor_get(v_a_315_, 1);
v_currMacroScope_360_ = lean_ctor_get(v_a_315_, 2);
v_ref_361_ = lean_ctor_get(v_a_315_, 5);
v___x_362_ = l_Lean_Syntax_getArg(v___x_323_, v___x_321_);
lean_dec(v___x_323_);
v___x_363_ = l_Lean_SourceInfo_fromRef(v_ref_361_, v___x_324_);
v___x_364_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
v___x_365_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_366_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
lean_inc_n(v_currMacroScope_360_, 2);
lean_inc_n(v_quotContext_359_, 2);
v___x_367_ = l_Lean_addMacroScope(v_quotContext_359_, v___x_366_, v_currMacroScope_360_);
v___x_368_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_363_, 3);
v___x_369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_369_, 0, v___x_363_);
lean_ctor_set(v___x_369_, 1, v___x_365_);
lean_ctor_set(v___x_369_, 2, v___x_367_);
lean_ctor_set(v___x_369_, 3, v___x_368_);
v___x_370_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_371_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
v___x_372_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11));
v___x_373_ = l_Lean_addMacroScope(v_quotContext_359_, v___x_372_, v_currMacroScope_360_);
v___x_374_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16));
v___x_375_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_375_, 0, v___x_363_);
lean_ctor_set(v___x_375_, 1, v___x_371_);
lean_ctor_set(v___x_375_, 2, v___x_373_);
lean_ctor_set(v___x_375_, 3, v___x_374_);
v___x_376_ = l_Lean_Syntax_node2(v___x_363_, v___x_370_, v___x_362_, v___x_375_);
v___x_377_ = l_Lean_Syntax_node2(v___x_363_, v___x_364_, v___x_369_, v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_a_316_);
return v___x_378_;
}
}
else
{
lean_object* v_quotContext_379_; lean_object* v_currMacroScope_380_; lean_object* v_ref_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v___x_323_);
v_quotContext_379_ = lean_ctor_get(v_a_315_, 1);
v_currMacroScope_380_ = lean_ctor_get(v_a_315_, 2);
v_ref_381_ = lean_ctor_get(v_a_315_, 5);
v___x_382_ = 0;
v___x_383_ = l_Lean_SourceInfo_fromRef(v_ref_381_, v___x_382_);
v___x_384_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
v___x_385_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11));
lean_inc(v_currMacroScope_380_);
lean_inc(v_quotContext_379_);
v___x_386_ = l_Lean_addMacroScope(v_quotContext_379_, v___x_385_, v_currMacroScope_380_);
v___x_387_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16));
v___x_388_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_388_, 0, v___x_383_);
lean_ctor_set(v___x_388_, 1, v___x_384_);
lean_ctor_set(v___x_388_, 2, v___x_386_);
lean_ctor_set(v___x_388_, 3, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_a_316_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___boxed(lean_object* v_x_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(v_x_390_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg(lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_396_ = 0;
v___x_397_ = l_Lean_SourceInfo_fromRef(v_a_394_, v___x_396_);
v___x_398_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
v___x_399_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_397_, 3);
v___x_400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_397_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_402_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_403_, 0, v___x_397_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
v___x_404_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_397_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_Syntax_node3(v___x_397_, v___x_398_, v___x_400_, v___x_403_, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_395_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___redArg___boxed(lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_408_, v_a_409_);
lean_dec(v_a_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil(lean_object* v_x_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_412_, v_a_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNil___boxed(lean_object* v_x_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Internal_Do_unexpandEPostNil(v_x_415_, v_a_416_, v_a_417_);
lean_dec(v_a_416_);
lean_dec(v_x_415_);
return v_res_418_;
}
}
static lean_object* _init_l_Std_Internal_Do_unexpandEPostCons___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11));
v___x_424_ = ((lean_object*)(l_Std_Internal_Do_unexpandEPostCons___closed__1));
v___x_425_ = l_Lean_addMacroScope(v___x_424_, v___x_423_, v___x_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons(lean_object* v_x_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
lean_inc(v_x_426_);
v___x_430_ = l_Lean_Syntax_isOfKind(v_x_426_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_x_426_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_a_428_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = l_Lean_Syntax_getArg(v_x_426_, v___x_433_);
lean_dec(v_x_426_);
v___x_435_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_434_);
v___x_436_ = l_Lean_Syntax_matchesNull(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_a_428_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = l_Lean_Syntax_getArg(v___x_434_, v___x_439_);
v___x_441_ = l_Lean_Syntax_getArg(v___x_434_, v___x_433_);
lean_dec(v___x_434_);
v___x_442_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4));
lean_inc(v___x_441_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_444_ = l_Lean_SourceInfo_fromRef(v_a_427_, v___x_443_);
v___x_445_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_446_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostCons___closed__2, &l_Std_Internal_Do_unexpandEPostCons___closed__2_once, _init_l_Std_Internal_Do_unexpandEPostCons___closed__2);
v___x_447_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_444_, 2);
v___x_448_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_445_);
lean_ctor_set(v___x_448_, 2, v___x_446_);
lean_ctor_set(v___x_448_, 3, v___x_447_);
v___x_449_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_450_ = l_Lean_Syntax_node2(v___x_444_, v___x_449_, v___x_440_, v___x_441_);
v___x_451_ = l_Lean_Syntax_node2(v___x_444_, v___x_429_, v___x_448_, v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_a_428_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = l_Lean_Syntax_getArg(v___x_441_, v___x_433_);
lean_inc(v___x_453_);
v___x_454_ = l_Lean_Syntax_matchesNull(v___x_453_, v___x_439_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
lean_inc(v___x_453_);
v___x_455_ = l_Lean_Syntax_matchesNull(v___x_453_, v___x_433_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = l_Lean_Syntax_getNumArgs(v___x_453_);
v___x_457_ = lean_nat_dec_le(v___x_435_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v___x_456_);
lean_dec(v___x_453_);
v___x_458_ = l_Lean_SourceInfo_fromRef(v_a_427_, v___x_455_);
v___x_459_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
v___x_460_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostCons___closed__2, &l_Std_Internal_Do_unexpandEPostCons___closed__2_once, _init_l_Std_Internal_Do_unexpandEPostCons___closed__2);
v___x_461_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16));
lean_inc_n(v___x_458_, 2);
v___x_462_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_462_, 0, v___x_458_);
lean_ctor_set(v___x_462_, 1, v___x_459_);
lean_ctor_set(v___x_462_, 2, v___x_460_);
lean_ctor_set(v___x_462_, 3, v___x_461_);
v___x_463_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_464_ = l_Lean_Syntax_node2(v___x_458_, v___x_463_, v___x_440_, v___x_441_);
v___x_465_ = l_Lean_Syntax_node2(v___x_458_, v___x_429_, v___x_462_, v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_a_428_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v___x_441_);
v___x_467_ = l_Lean_Syntax_getArg(v___x_453_, v___x_439_);
v___x_468_ = l_Lean_Syntax_getArgs(v___x_453_);
lean_dec(v___x_453_);
v___x_469_ = l_Array_extract___redArg(v___x_468_, v___x_435_, v___x_456_);
lean_dec_ref(v___x_468_);
v___x_470_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_471_ = lean_box(2);
v___x_472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_469_);
v___x_473_ = l_Lean_Syntax_getArgs(v___x_472_);
lean_dec_ref_known(v___x_472_, 3);
v___x_474_ = l_Lean_SourceInfo_fromRef(v_a_427_, v___x_455_);
v___x_475_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_474_, 4);
v___x_476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_474_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
lean_inc_ref(v___x_478_);
v___x_479_ = l_Array_mkArray4___redArg(v___x_440_, v___x_478_, v___x_467_, v___x_478_);
v___x_480_ = l_Array_append___redArg(v___x_479_, v___x_473_);
lean_dec_ref(v___x_473_);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_474_);
lean_ctor_set(v___x_481_, 1, v___x_470_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
v___x_482_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_474_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_Syntax_node3(v___x_474_, v___x_442_, v___x_476_, v___x_481_, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_a_428_);
return v___x_485_;
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_441_);
v___x_486_ = l_Lean_Syntax_getArg(v___x_453_, v___x_439_);
lean_dec(v___x_453_);
v___x_487_ = l_Lean_SourceInfo_fromRef(v_a_427_, v___x_454_);
v___x_488_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_487_, 4);
v___x_489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_491_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_487_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_Syntax_node3(v___x_487_, v___x_490_, v___x_440_, v___x_492_, v___x_486_);
v___x_494_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_487_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Lean_Syntax_node3(v___x_487_, v___x_442_, v___x_489_, v___x_493_, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_a_428_);
return v___x_497_;
}
}
else
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___x_453_);
lean_dec(v___x_441_);
v___x_498_ = 0;
v___x_499_ = l_Lean_SourceInfo_fromRef(v_a_427_, v___x_498_);
v___x_500_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7));
lean_inc_n(v___x_499_, 3);
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_503_ = l_Lean_Syntax_node1(v___x_499_, v___x_502_, v___x_440_);
v___x_504_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_499_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_Syntax_node3(v___x_499_, v___x_442_, v___x_501_, v___x_503_, v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_a_428_);
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostCons___boxed(lean_object* v_x_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_Internal_Do_unexpandEPostCons(v_x_508_, v_a_509_, v_a_510_);
lean_dec(v_a_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg(lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_514_ = 0;
v___x_515_ = l_Lean_SourceInfo_fromRef(v_a_512_, v___x_514_);
v___x_516_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
v___x_517_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_515_, 3);
v___x_518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_515_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_520_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
v___x_521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_521_, 0, v___x_515_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
v___x_522_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_515_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_Syntax_node3(v___x_515_, v___x_516_, v___x_518_, v___x_521_, v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_a_513_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___redArg___boxed(lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_526_, v_a_527_);
lean_dec(v_a_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk(lean_object* v_x_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_530_, v_a_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostNilMk___boxed(lean_object* v_x_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_Internal_Do_unexpandEPostNilMk(v_x_533_, v_a_534_, v_a_535_);
lean_dec(v_a_534_);
lean_dec(v_x_533_);
return v_res_536_;
}
}
static lean_object* _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3));
v___x_539_ = ((lean_object*)(l_Std_Internal_Do_unexpandEPostCons___closed__1));
v___x_540_ = l_Lean_addMacroScope(v___x_539_, v___x_538_, v___x_537_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk(lean_object* v_x_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6));
lean_inc(v_x_541_);
v___x_545_ = l_Lean_Syntax_isOfKind(v_x_541_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v_x_541_);
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v_a_543_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = l_Lean_Syntax_getArg(v_x_541_, v___x_548_);
lean_dec(v_x_541_);
v___x_550_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_549_);
v___x_551_ = l_Lean_Syntax_matchesNull(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_543_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = l_Lean_Syntax_getArg(v___x_549_, v___x_554_);
v___x_556_ = l_Lean_Syntax_getArg(v___x_549_, v___x_548_);
lean_dec(v___x_549_);
v___x_557_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1));
lean_inc(v___x_556_);
v___x_558_ = l_Lean_Syntax_isOfKind(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_559_ = l_Lean_SourceInfo_fromRef(v_a_542_, v___x_558_);
v___x_560_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_561_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostConsMk___closed__0, &l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once, _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0);
v___x_562_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_559_, 2);
v___x_563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_563_, 0, v___x_559_);
lean_ctor_set(v___x_563_, 1, v___x_560_);
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 3, v___x_562_);
v___x_564_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_565_ = l_Lean_Syntax_node2(v___x_559_, v___x_564_, v___x_555_, v___x_556_);
v___x_566_ = l_Lean_Syntax_node2(v___x_559_, v___x_544_, v___x_563_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_a_543_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = l_Lean_Syntax_getArg(v___x_556_, v___x_548_);
lean_inc(v___x_568_);
v___x_569_ = l_Lean_Syntax_matchesNull(v___x_568_, v___x_554_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; 
lean_inc(v___x_568_);
v___x_570_ = l_Lean_Syntax_matchesNull(v___x_568_, v___x_548_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = l_Lean_Syntax_getNumArgs(v___x_568_);
v___x_572_ = lean_nat_dec_le(v___x_550_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___x_571_);
lean_dec(v___x_568_);
v___x_573_ = l_Lean_SourceInfo_fromRef(v_a_542_, v___x_570_);
v___x_574_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1, &l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
v___x_575_ = lean_obj_once(&l_Std_Internal_Do_unexpandEPostConsMk___closed__0, &l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once, _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0);
v___x_576_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8));
lean_inc_n(v___x_573_, 2);
v___x_577_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_577_, 0, v___x_573_);
lean_ctor_set(v___x_577_, 1, v___x_574_);
lean_ctor_set(v___x_577_, 2, v___x_575_);
lean_ctor_set(v___x_577_, 3, v___x_576_);
v___x_578_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_579_ = l_Lean_Syntax_node2(v___x_573_, v___x_578_, v___x_555_, v___x_556_);
v___x_580_ = l_Lean_Syntax_node2(v___x_573_, v___x_544_, v___x_577_, v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_a_543_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v___x_556_);
v___x_582_ = l_Lean_Syntax_getArg(v___x_568_, v___x_554_);
v___x_583_ = l_Lean_Syntax_getArgs(v___x_568_);
lean_dec(v___x_568_);
v___x_584_ = l_Array_extract___redArg(v___x_583_, v___x_550_, v___x_571_);
lean_dec_ref(v___x_583_);
v___x_585_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_586_ = lean_box(2);
v___x_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
lean_ctor_set(v___x_587_, 2, v___x_584_);
v___x_588_ = l_Lean_Syntax_getArgs(v___x_587_);
lean_dec_ref_known(v___x_587_, 3);
v___x_589_ = l_Lean_SourceInfo_fromRef(v_a_542_, v___x_570_);
v___x_590_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_589_, 4);
v___x_591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_589_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_inc_ref(v___x_593_);
v___x_594_ = l_Array_mkArray4___redArg(v___x_555_, v___x_593_, v___x_582_, v___x_593_);
v___x_595_ = l_Array_append___redArg(v___x_594_, v___x_588_);
lean_dec_ref(v___x_588_);
v___x_596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_596_, 0, v___x_589_);
lean_ctor_set(v___x_596_, 1, v___x_585_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
v___x_597_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_589_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_Syntax_node3(v___x_589_, v___x_557_, v___x_591_, v___x_596_, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v_a_543_);
return v___x_600_;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v___x_556_);
v___x_601_ = l_Lean_Syntax_getArg(v___x_568_, v___x_554_);
lean_dec(v___x_568_);
v___x_602_ = l_Lean_SourceInfo_fromRef(v_a_542_, v___x_569_);
v___x_603_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_602_, 4);
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_606_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_602_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_Syntax_node3(v___x_602_, v___x_605_, v___x_555_, v___x_607_, v___x_601_);
v___x_609_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_602_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_Syntax_node3(v___x_602_, v___x_557_, v___x_604_, v___x_608_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_a_543_);
return v___x_612_;
}
}
else
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v___x_568_);
lean_dec(v___x_556_);
v___x_613_ = 0;
v___x_614_ = l_Lean_SourceInfo_fromRef(v_a_542_, v___x_613_);
v___x_615_ = ((lean_object*)(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2));
lean_inc_n(v___x_614_, 3);
v___x_616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1));
v___x_618_ = l_Lean_Syntax_node1(v___x_614_, v___x_617_, v___x_555_);
v___x_619_ = ((lean_object*)(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17));
v___x_620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_614_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l_Lean_Syntax_node3(v___x_614_, v___x_557_, v___x_616_, v___x_618_, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_543_);
return v___x_622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandEPostConsMk___boxed(lean_object* v_x_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Internal_Do_unexpandEPostConsMk(v_x_623_, v_a_624_, v_a_625_);
lean_dec(v_a_624_);
return v_res_626_;
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
