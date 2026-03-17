// Lean compiler output
// Module: Std.Do.SPred.Notation
// Imports: public meta import Std.Do.SPred.Notation.Basic public import Std.Do.SPred.Notation.Basic
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_expandExplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term_u231c___u231d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__0 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value;
static const lean_string_object l_Std_Do_term_u231c___u231d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__1 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value;
static const lean_string_object l_Std_Do_term_u231c___u231d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term⌜_⌝"};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__2 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__2_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__3_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__3_value_aux_1),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 155, 137, 127, 35, 248, 173, 10)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__3 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__3_value;
static const lean_string_object l_Std_Do_term_u231c___u231d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__4 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__4_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__5 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__5_value;
static const lean_string_object l_Std_Do_term_u231c___u231d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌜"};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__6 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__6_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__6_value)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__7 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__7_value;
static const lean_string_object l_Std_Do_term_u231c___u231d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__8 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__8_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__9 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__9_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__10 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__10_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__5_value),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__7_value),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__10_value)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__11 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__11_value;
static const lean_string_object l_Std_Do_term_u231c___u231d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌝"};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__12 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__12_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__12_value)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__13 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__13_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__5_value),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__11_value),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__13_value)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__14 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__14_value;
static const lean_ctor_object l_Std_Do_term_u231c___u231d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__14_value)}};
static const lean_object* l_Std_Do_term_u231c___u231d___closed__15 = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__15_value;
LEAN_EXPORT const lean_object* l_Std_Do_term_u231c___u231d = (const lean_object*)&l_Std_Do_term_u231c___u231d___closed__15_value;
static const lean_string_object l_Std_Do_term___u22a2_u209b___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_⊢ₛ_"};
static const lean_object* l_Std_Do_term___u22a2_u209b___00__closed__0 = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209b___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u22a2_u209b___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u22a2_u209b___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 64, 157, 81, 47, 23, 235, 108)}};
static const lean_object* l_Std_Do_term___u22a2_u209b___00__closed__1 = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u22a2_u209b___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " ⊢ₛ "};
static const lean_object* l_Std_Do_term___u22a2_u209b___00__closed__2 = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209b___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u22a2_u209b___00__closed__3 = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209b___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__9_value),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_Std_Do_term___u22a2_u209b___00__closed__4 = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209b___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__5_value),((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__3_value),((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u22a2_u209b___00__closed__5 = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__5_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209b___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__5_value)}};
static const lean_object* l_Std_Do_term___u22a2_u209b___00__closed__6 = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u22a2_u209b__ = (const lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__6_value;
static const lean_string_object l_Std_Do_term_u22a2_u209b___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term⊢ₛ_"};
static const lean_object* l_Std_Do_term_u22a2_u209b___00__closed__0 = (const lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term_u22a2_u209b___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term_u22a2_u209b___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term_u22a2_u209b___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 33, 26, 243, 26, 184, 240, 184)}};
static const lean_object* l_Std_Do_term_u22a2_u209b___00__closed__1 = (const lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__1_value;
static const lean_string_object l_Std_Do_term_u22a2_u209b___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 3, .m_data = "⊢ₛ "};
static const lean_object* l_Std_Do_term_u22a2_u209b___00__closed__2 = (const lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term_u22a2_u209b___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__2_value)}};
static const lean_object* l_Std_Do_term_u22a2_u209b___00__closed__3 = (const lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term_u22a2_u209b___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__5_value),((lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__3_value),((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__4_value)}};
static const lean_object* l_Std_Do_term_u22a2_u209b___00__closed__4 = (const lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term_u22a2_u209b___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__4_value)}};
static const lean_object* l_Std_Do_term_u22a2_u209b___00__closed__5 = (const lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Do_term_u22a2_u209b__ = (const lean_object*)&l_Std_Do_term_u22a2_u209b___00__closed__5_value;
static const lean_string_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 9, .m_data = "term_⊣⊢ₛ_"};
static const lean_object* l_Std_Do_term___u22a3_u22a2_u209b___00__closed__0 = (const lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 122, 29, 216, 46, 173, 32, 216)}};
static const lean_object* l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1 = (const lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 5, .m_data = " ⊣⊢ₛ "};
static const lean_object* l_Std_Do_term___u22a3_u22a2_u209b___00__closed__2 = (const lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u22a3_u22a2_u209b___00__closed__3 = (const lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term_u231c___u231d___closed__5_value),((lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__3_value),((lean_object*)&l_Std_Do_term___u22a2_u209b___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u22a3_u22a2_u209b___00__closed__4 = (const lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u22a3_u22a2_u209b___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u22a3_u22a2_u209b___00__closed__5 = (const lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u22a3_u22a2_u209b__ = (const lean_object*)&l_Std_Do_term___u22a3_u22a2_u209b___00__closed__5_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "SPred.pure"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__5_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__8_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__9_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(16, 115, 190, 26, 167, 150, 203, 221)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__9_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(83, 183, 133, 62, 214, 202, 136, 98)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__11_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__10_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__12_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__13 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__13_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__11_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__13_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__14 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__14_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__15 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__15_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SPred.entails"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 27, 24, 221, 87, 233, 202, 140)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 181, 97, 38, 147, 213, 38, 7)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__4_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__6_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__7_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__5_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__7_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termSpred(_)"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__9_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(76, 240, 91, 148, 237, 191, 255, 193)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "spred("};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∧_"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__0_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 224, 85, 99, 168, 124, 84, 223)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∨_"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(44, 23, 28, 64, 30, 253, 248, 167)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 6, .m_data = "term¬_"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(222, 122, 71, 36, 131, 84, 176, 236)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__6_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_↔_"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__8_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(220, 124, 41, 198, 228, 162, 237, 244)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term∃_,_"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__10_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(224, 105, 219, 112, 166, 139, 167, 161)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__12_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(195, 142, 115, 15, 55, 103, 31, 115)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "SPred.forall"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__14 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__14_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(189, 183, 85, 87, 105, 38, 9, 95)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(118, 145, 1, 190, 19, 10, 144, 159)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__18 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__18_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__20 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__20_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__22 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__22_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__25 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__25_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__27 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__27_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__29_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__29 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__29_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__29_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__30 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__30_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__31 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__31_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__32_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__32 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__32_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__32_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__33 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__33_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__34_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__34 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__34_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__34_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__35 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__35_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__36 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__36_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__37_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__37 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__37_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__37_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__38 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__38_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__39 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__39_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__39_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__40 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__40_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__41 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__41_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__38_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__41_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__42 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__42_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__35_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__42_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__43 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__43_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__33_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__43_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__44 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__44_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__30_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__44_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__48 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__48_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__54 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__54_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__57 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__57_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__59 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__59_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__61 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__61_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__61_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exists"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(119, 199, 194, 26, 176, 147, 16, 83)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "SPred.iff"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__68 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__68_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "iff"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__70 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__70_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(216, 213, 73, 68, 36, 234, 63, 232)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(27, 79, 214, 161, 232, 72, 176, 24)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__72_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__73 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__73_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__73_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__74 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__74_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "SPred.imp"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__75 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__75_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "imp"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__77 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__77_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__77_value),LEAN_SCALAR_PTR_LITERAL(229, 78, 255, 122, 125, 47, 236, 91)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__77_value),LEAN_SCALAR_PTR_LITERAL(254, 180, 127, 119, 35, 232, 80, 131)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__80 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__80_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__80_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__81 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__81_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "SPred.not"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__82 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__82_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__84 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__84_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(75, 43, 215, 201, 164, 208, 115, 204)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(104, 148, 110, 90, 206, 151, 192, 189)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__87 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__87_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__86_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__88 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__88_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__88_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__89 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__89_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__87_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__89_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__90 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__90_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "SPred.or"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__91 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__91_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__93 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__93_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__93_value),LEAN_SCALAR_PTR_LITERAL(1, 253, 51, 240, 68, 70, 110, 158)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__93_value),LEAN_SCALAR_PTR_LITERAL(114, 97, 84, 180, 109, 220, 63, 60)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__95_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__96 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__96_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__96_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__97 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__97_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "SPred.and"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__98 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__98_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__100 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__100_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(27, 27, 184, 174, 232, 138, 92, 103)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(216, 97, 27, 109, 96, 85, 230, 202)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__102_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__103 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__103_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__104 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__104_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__3_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__5_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "SPred.bientails"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bientails"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 193, 89, 51, 91, 176, 2, 152)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(218, 255, 192, 203, 199, 147, 226, 14)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 51, 221, 5, 242, 131, 169, 118)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__1 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__1_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__2 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__2_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_fakeMod"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__4 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__4_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(168, 44, 241, 255, 153, 255, 67, 53)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__5 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__5_value;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Notation"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__7 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__7_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(66, 246, 126, 200, 193, 235, 124, 8)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__8_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__9 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__9_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__10 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__10_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__38_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__10_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__11 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__11_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__35_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__11_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__12 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__12_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__33_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__12_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__13 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__13_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__9_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__13_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__15 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__15_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__16 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__16_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__17 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__17_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandEntails___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "⊢ₛ"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandEntails___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandEntails___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandBientails___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 3, .m_data = "⊣⊢ₛ"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandBientails___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandBientails___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∧"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandAnd___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandAnd___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∨"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandOr___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandOr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandNot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "¬"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandNot___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandNot___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandImp___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandImp___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∃"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandExists___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandExists___closed__0_value;
static const lean_string_object l_Std_Do_SPred_Notation_unexpandExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unbracketedExplicitBinders"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandExists___closed__1 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandExists___closed__1_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unexpandExists___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unexpandExists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unexpandExists___closed__2_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unexpandExists___closed__1_value),LEAN_SCALAR_PTR_LITERAL(187, 220, 119, 82, 242, 112, 119, 200)}};
static const lean_object* l_Std_Do_SPred_Notation_unexpandExists___closed__2 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandExists___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unexpandIff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↔"};
static const lean_object* l_Std_Do_SPred_Notation_unexpandIff___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unexpandIff___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__5));
v___x_102_ = l_String_toRawSubstring_x27(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1(lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
lean_inc(v_x_127_);
v___x_131_ = l_Lean_Syntax_isOfKind(v_x_127_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec_ref(v_a_128_);
lean_dec(v_x_127_);
v___x_132_ = lean_box(1);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_a_129_);
return v___x_133_;
}
else
{
lean_object* v_quotContext_134_; lean_object* v_currMacroScope_135_; lean_object* v_ref_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_quotContext_134_ = lean_ctor_get(v_a_128_, 1);
lean_inc(v_quotContext_134_);
v_currMacroScope_135_ = lean_ctor_get(v_a_128_, 2);
lean_inc(v_currMacroScope_135_);
v_ref_136_ = lean_ctor_get(v_a_128_, 5);
lean_inc(v_ref_136_);
lean_dec_ref(v_a_128_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = l_Lean_Syntax_getArg(v_x_127_, v___x_137_);
lean_dec(v_x_127_);
v___x_139_ = 0;
v___x_140_ = l_Lean_SourceInfo_fromRef(v_ref_136_, v___x_139_);
lean_dec(v_ref_136_);
v___x_141_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_142_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6);
v___x_143_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__9));
v___x_144_ = l_Lean_addMacroScope(v_quotContext_134_, v___x_143_, v_currMacroScope_135_);
v___x_145_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__14));
lean_inc(v___x_140_);
v___x_146_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_146_, 0, v___x_140_);
lean_ctor_set(v___x_146_, 1, v___x_142_);
lean_ctor_set(v___x_146_, 2, v___x_144_);
lean_ctor_set(v___x_146_, 3, v___x_145_);
v___x_147_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
lean_inc(v___x_140_);
v___x_148_ = l_Lean_Syntax_node1(v___x_140_, v___x_147_, v___x_138_);
v___x_149_ = l_Lean_Syntax_node2(v___x_140_, v___x_141_, v___x_146_, v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_129_);
return v___x_150_;
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__0));
v___x_153_ = l_String_toRawSubstring_x27(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1(lean_object* v_x_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
lean_inc(v_x_181_);
v___x_185_ = l_Lean_Syntax_isOfKind(v_x_181_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec_ref(v_a_182_);
lean_dec(v_x_181_);
v___x_186_ = lean_box(1);
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_a_183_);
return v___x_187_;
}
else
{
lean_object* v_quotContext_188_; lean_object* v_currMacroScope_189_; lean_object* v_ref_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_quotContext_188_ = lean_ctor_get(v_a_182_, 1);
lean_inc(v_quotContext_188_);
v_currMacroScope_189_ = lean_ctor_get(v_a_182_, 2);
lean_inc(v_currMacroScope_189_);
v_ref_190_ = lean_ctor_get(v_a_182_, 5);
lean_inc(v_ref_190_);
lean_dec_ref(v_a_182_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l_Lean_Syntax_getArg(v_x_181_, v___x_191_);
v___x_193_ = lean_unsigned_to_nat(2u);
v___x_194_ = l_Lean_Syntax_getArg(v_x_181_, v___x_193_);
lean_dec(v_x_181_);
v___x_195_ = 0;
v___x_196_ = l_Lean_SourceInfo_fromRef(v_ref_190_, v___x_195_);
lean_dec(v_ref_190_);
v___x_197_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_198_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1);
v___x_199_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3));
v___x_200_ = l_Lean_addMacroScope(v_quotContext_188_, v___x_199_, v_currMacroScope_189_);
v___x_201_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8));
lean_inc(v___x_196_);
v___x_202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_202_, 0, v___x_196_);
lean_ctor_set(v___x_202_, 1, v___x_198_);
lean_ctor_set(v___x_202_, 2, v___x_200_);
lean_ctor_set(v___x_202_, 3, v___x_201_);
v___x_203_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_204_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_205_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_196_);
v___x_206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_196_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_196_);
v___x_208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_196_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_inc_ref(v___x_208_);
lean_inc_ref(v___x_206_);
lean_inc(v___x_196_);
v___x_209_ = l_Lean_Syntax_node3(v___x_196_, v___x_204_, v___x_206_, v___x_192_, v___x_208_);
lean_inc(v___x_196_);
v___x_210_ = l_Lean_Syntax_node3(v___x_196_, v___x_204_, v___x_206_, v___x_194_, v___x_208_);
lean_inc(v___x_196_);
v___x_211_ = l_Lean_Syntax_node2(v___x_196_, v___x_203_, v___x_209_, v___x_210_);
v___x_212_ = l_Lean_Syntax_node2(v___x_196_, v___x_197_, v___x_202_, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_183_);
return v___x_213_;
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__14));
v___x_243_ = l_String_toRawSubstring_x27(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__27));
v___x_276_ = l_String_toRawSubstring_x27(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Array_mkArray0(lean_box(0));
return v___x_330_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__68));
v___x_369_ = l_String_toRawSubstring_x27(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__75));
v___x_387_ = l_String_toRawSubstring_x27(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__82));
v___x_405_ = l_String_toRawSubstring_x27(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__91));
v___x_428_ = l_String_toRawSubstring_x27(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__98));
v___x_446_ = l_String_toRawSubstring_x27(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1(lean_object* v_x_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___y_466_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
lean_inc(v_x_462_);
v___x_470_ = l_Lean_Syntax_isOfKind(v_x_462_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec_ref(v_a_463_);
lean_dec(v_x_462_);
v___x_471_ = lean_box(1);
v___x_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_a_464_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = l_Lean_Syntax_getArg(v_x_462_, v___x_474_);
lean_dec(v_x_462_);
v___x_476_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1));
lean_inc(v___x_475_);
v___x_477_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3));
lean_inc(v___x_475_);
v___x_479_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5));
lean_inc(v___x_475_);
v___x_481_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7));
lean_inc(v___x_475_);
v___x_483_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9));
lean_inc(v___x_475_);
v___x_485_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11));
lean_inc(v___x_475_);
v___x_487_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v_x_490_; lean_object* v_xs_491_; lean_object* v_P_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_x_546_; lean_object* v_ty_547_; lean_object* v_xs_548_; lean_object* v_P_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v_x_608_; lean_object* v_xs_609_; lean_object* v_ty_610_; lean_object* v_ys_611_; lean_object* v_P_612_; lean_object* v___y_613_; lean_object* v___y_614_; uint8_t v___x_676_; 
v___x_488_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13));
lean_inc(v___x_475_);
v___x_676_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_488_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___x_677_ = lean_box(1);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_a_464_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = l_Lean_Syntax_getArg(v___x_475_, v___x_474_);
lean_inc(v___x_679_);
v___x_680_ = l_Lean_Syntax_matchesNull(v___x_679_, v___x_474_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = l_Lean_Syntax_getNumArgs(v___x_679_);
v___x_682_ = lean_nat_dec_le(v___x_474_, v___x_681_);
if (v___x_682_ == 0)
{
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v_x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_x_683_ = l_Lean_Syntax_getArg(v___x_679_, v___x_473_);
v___x_684_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_683_);
v___x_685_ = l_Lean_Syntax_isOfKind(v_x_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_683_);
v___x_687_ = l_Lean_Syntax_isOfKind(v_x_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = l_Lean_Syntax_getArg(v_x_683_, v___x_474_);
lean_inc(v___x_688_);
v___x_689_ = l_Lean_Syntax_matchesNull(v___x_688_, v___x_474_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = l_Lean_Syntax_getNumArgs(v___x_688_);
v___x_691_ = lean_nat_dec_le(v___x_474_, v___x_690_);
if (v___x_691_ == 0)
{
lean_dec(v___x_690_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v_x_692_; uint8_t v___x_693_; 
v_x_692_ = l_Lean_Syntax_getArg(v___x_688_, v___x_473_);
lean_inc(v_x_692_);
v___x_693_ = l_Lean_Syntax_isOfKind(v_x_692_, v___x_684_);
if (v___x_693_ == 0)
{
lean_dec(v_x_692_);
lean_dec(v___x_690_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_unsigned_to_nat(2u);
v___x_695_ = l_Lean_Syntax_getArg(v_x_683_, v___x_694_);
lean_inc(v___x_695_);
v___x_696_ = l_Lean_Syntax_matchesNull(v___x_695_, v___x_694_);
if (v___x_696_ == 0)
{
lean_dec(v___x_695_);
lean_dec(v_x_692_);
lean_dec(v___x_690_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_unsigned_to_nat(3u);
v___x_698_ = l_Lean_Syntax_getArg(v_x_683_, v___x_697_);
lean_dec(v_x_683_);
v___x_699_ = l_Lean_Syntax_matchesNull(v___x_698_, v___x_473_);
if (v___x_699_ == 0)
{
lean_dec(v___x_695_);
lean_dec(v_x_692_);
lean_dec(v___x_690_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = l_Lean_Syntax_getArg(v___x_475_, v___x_694_);
v___x_701_ = l_Lean_Syntax_matchesNull(v___x_700_, v___x_473_);
if (v___x_701_ == 0)
{
lean_dec(v___x_695_);
lean_dec(v_x_692_);
lean_dec(v___x_690_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_ty_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_P_712_; lean_object* v_ys_713_; lean_object* v_xs_714_; 
v___x_702_ = l_Lean_Syntax_getArgs(v___x_688_);
lean_dec(v___x_688_);
v___x_703_ = l_Array_extract___redArg(v___x_702_, v___x_474_, v___x_690_);
lean_dec_ref(v___x_702_);
v_ty_704_ = l_Lean_Syntax_getArg(v___x_695_, v___x_474_);
lean_dec(v___x_695_);
v___x_705_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_706_ = lean_box(2);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
lean_ctor_set(v___x_707_, 2, v___x_703_);
v___x_708_ = lean_unsigned_to_nat(4u);
v___x_709_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_710_ = l_Array_extract___redArg(v___x_709_, v___x_474_, v___x_681_);
lean_dec_ref(v___x_709_);
v___x_711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_706_);
lean_ctor_set(v___x_711_, 1, v___x_705_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
v_P_712_ = l_Lean_Syntax_getArg(v___x_475_, v___x_708_);
lean_dec(v___x_475_);
v_ys_713_ = l_Lean_Syntax_getArgs(v___x_711_);
lean_dec_ref(v___x_711_);
v_xs_714_ = l_Lean_Syntax_getArgs(v___x_707_);
lean_dec_ref(v___x_707_);
v_x_608_ = v_x_692_;
v_xs_609_ = v_xs_714_;
v_ty_610_ = v_ty_704_;
v_ys_611_ = v_ys_713_;
v_P_612_ = v_P_712_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_x_715_; uint8_t v___x_716_; 
v_x_715_ = l_Lean_Syntax_getArg(v___x_688_, v___x_473_);
lean_inc(v_x_715_);
v___x_716_ = l_Lean_Syntax_isOfKind(v_x_715_, v___x_684_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = l_Lean_Syntax_getNumArgs(v___x_688_);
v___x_718_ = lean_nat_dec_le(v___x_474_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v___x_717_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_716_ == 0)
{
lean_dec(v___x_717_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(2u);
v___x_720_ = l_Lean_Syntax_getArg(v_x_683_, v___x_719_);
lean_inc(v___x_720_);
v___x_721_ = l_Lean_Syntax_matchesNull(v___x_720_, v___x_719_);
if (v___x_721_ == 0)
{
lean_dec(v___x_720_);
lean_dec(v___x_717_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_unsigned_to_nat(3u);
v___x_723_ = l_Lean_Syntax_getArg(v_x_683_, v___x_722_);
lean_dec(v_x_683_);
v___x_724_ = l_Lean_Syntax_matchesNull(v___x_723_, v___x_473_);
if (v___x_724_ == 0)
{
lean_dec(v___x_720_);
lean_dec(v___x_717_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = l_Lean_Syntax_getArg(v___x_475_, v___x_719_);
v___x_726_ = l_Lean_Syntax_matchesNull(v___x_725_, v___x_473_);
if (v___x_726_ == 0)
{
lean_dec(v___x_720_);
lean_dec(v___x_717_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_P_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_ty_737_; lean_object* v_ys_738_; lean_object* v_xs_739_; 
v___x_727_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_728_ = l_Array_extract___redArg(v___x_727_, v___x_474_, v___x_681_);
lean_dec_ref(v___x_727_);
v___x_729_ = lean_unsigned_to_nat(4u);
v___x_730_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_731_ = lean_box(2);
v___x_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
lean_ctor_set(v___x_732_, 2, v___x_728_);
v_P_733_ = l_Lean_Syntax_getArg(v___x_475_, v___x_729_);
lean_dec(v___x_475_);
v___x_734_ = l_Lean_Syntax_getArgs(v___x_688_);
lean_dec(v___x_688_);
v___x_735_ = l_Array_extract___redArg(v___x_734_, v___x_474_, v___x_717_);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_736_, 0, v___x_731_);
lean_ctor_set(v___x_736_, 1, v___x_730_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v_ty_737_ = l_Lean_Syntax_getArg(v___x_720_, v___x_474_);
lean_dec(v___x_720_);
v_ys_738_ = l_Lean_Syntax_getArgs(v___x_732_);
lean_dec_ref(v___x_732_);
v_xs_739_ = l_Lean_Syntax_getArgs(v___x_736_);
lean_dec_ref(v___x_736_);
v_x_608_ = v_x_715_;
v_xs_609_ = v_xs_739_;
v_ty_610_ = v_ty_737_;
v_ys_611_ = v_ys_738_;
v_P_612_ = v_P_733_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(2u);
v___x_741_ = l_Lean_Syntax_getArg(v_x_683_, v___x_740_);
lean_inc(v___x_741_);
v___x_742_ = l_Lean_Syntax_matchesNull(v___x_741_, v___x_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = l_Lean_Syntax_getNumArgs(v___x_688_);
v___x_744_ = lean_nat_dec_le(v___x_474_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v___x_743_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_716_ == 0)
{
lean_dec(v___x_743_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_742_ == 0)
{
lean_dec(v___x_743_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_unsigned_to_nat(3u);
v___x_746_ = l_Lean_Syntax_getArg(v_x_683_, v___x_745_);
lean_dec(v_x_683_);
v___x_747_ = l_Lean_Syntax_matchesNull(v___x_746_, v___x_473_);
if (v___x_747_ == 0)
{
lean_dec(v___x_743_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = l_Lean_Syntax_getArg(v___x_475_, v___x_740_);
v___x_749_ = l_Lean_Syntax_matchesNull(v___x_748_, v___x_473_);
if (v___x_749_ == 0)
{
lean_dec(v___x_743_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_P_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_ty_760_; lean_object* v_ys_761_; lean_object* v_xs_762_; 
v___x_750_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_751_ = l_Array_extract___redArg(v___x_750_, v___x_474_, v___x_681_);
lean_dec_ref(v___x_750_);
v___x_752_ = lean_unsigned_to_nat(4u);
v___x_753_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_754_ = lean_box(2);
v___x_755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
lean_ctor_set(v___x_755_, 2, v___x_751_);
v_P_756_ = l_Lean_Syntax_getArg(v___x_475_, v___x_752_);
lean_dec(v___x_475_);
v___x_757_ = l_Lean_Syntax_getArgs(v___x_688_);
lean_dec(v___x_688_);
v___x_758_ = l_Array_extract___redArg(v___x_757_, v___x_474_, v___x_743_);
lean_dec_ref(v___x_757_);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___x_754_);
lean_ctor_set(v___x_759_, 1, v___x_753_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
v_ty_760_ = l_Lean_Syntax_getArg(v___x_741_, v___x_474_);
lean_dec(v___x_741_);
v_ys_761_ = l_Lean_Syntax_getArgs(v___x_755_);
lean_dec_ref(v___x_755_);
v_xs_762_ = l_Lean_Syntax_getArgs(v___x_759_);
lean_dec_ref(v___x_759_);
v_x_608_ = v_x_715_;
v_xs_609_ = v_xs_762_;
v_ty_610_ = v_ty_760_;
v_ys_611_ = v_ys_761_;
v_P_612_ = v_P_756_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(3u);
v___x_764_ = l_Lean_Syntax_getArg(v_x_683_, v___x_763_);
lean_dec(v_x_683_);
v___x_765_ = l_Lean_Syntax_matchesNull(v___x_764_, v___x_473_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = l_Lean_Syntax_getNumArgs(v___x_688_);
v___x_767_ = lean_nat_dec_le(v___x_474_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v___x_766_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_716_ == 0)
{
lean_dec(v___x_766_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_742_ == 0)
{
lean_dec(v___x_766_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_765_ == 0)
{
lean_dec(v___x_766_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = l_Lean_Syntax_getArg(v___x_475_, v___x_740_);
v___x_769_ = l_Lean_Syntax_matchesNull(v___x_768_, v___x_473_);
if (v___x_769_ == 0)
{
lean_dec(v___x_766_);
lean_dec(v___x_741_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_P_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_ty_780_; lean_object* v_ys_781_; lean_object* v_xs_782_; 
v___x_770_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_771_ = l_Array_extract___redArg(v___x_770_, v___x_474_, v___x_681_);
lean_dec_ref(v___x_770_);
v___x_772_ = lean_unsigned_to_nat(4u);
v___x_773_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_774_ = lean_box(2);
v___x_775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
lean_ctor_set(v___x_775_, 2, v___x_771_);
v_P_776_ = l_Lean_Syntax_getArg(v___x_475_, v___x_772_);
lean_dec(v___x_475_);
v___x_777_ = l_Lean_Syntax_getArgs(v___x_688_);
lean_dec(v___x_688_);
v___x_778_ = l_Array_extract___redArg(v___x_777_, v___x_474_, v___x_766_);
lean_dec_ref(v___x_777_);
v___x_779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_779_, 0, v___x_774_);
lean_ctor_set(v___x_779_, 1, v___x_773_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
v_ty_780_ = l_Lean_Syntax_getArg(v___x_741_, v___x_474_);
lean_dec(v___x_741_);
v_ys_781_ = l_Lean_Syntax_getArgs(v___x_775_);
lean_dec_ref(v___x_775_);
v_xs_782_ = l_Lean_Syntax_getArgs(v___x_779_);
lean_dec_ref(v___x_779_);
v_x_608_ = v_x_715_;
v_xs_609_ = v_xs_782_;
v_ty_610_ = v_ty_780_;
v_ys_611_ = v_ys_781_;
v_P_612_ = v_P_776_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_ty_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_ty_783_ = l_Lean_Syntax_getArg(v___x_741_, v___x_474_);
lean_dec(v___x_741_);
v___x_784_ = lean_unsigned_to_nat(4u);
v___x_785_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_786_ = l_Array_extract___redArg(v___x_785_, v___x_474_, v___x_681_);
lean_dec_ref(v___x_785_);
v___x_787_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_788_ = lean_box(2);
v___x_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
lean_ctor_set(v___x_789_, 2, v___x_786_);
v___x_790_ = l_Lean_Syntax_getArg(v___x_475_, v___x_740_);
v___x_791_ = l_Lean_Syntax_matchesNull(v___x_790_, v___x_473_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = l_Lean_Syntax_getNumArgs(v___x_688_);
v___x_793_ = lean_nat_dec_le(v___x_474_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_ty_783_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_716_ == 0)
{
lean_dec(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_ty_783_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_742_ == 0)
{
lean_dec(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_ty_783_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_765_ == 0)
{
lean_dec(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_ty_783_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_791_ == 0)
{
lean_dec(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_ty_783_);
lean_dec(v_x_715_);
lean_dec(v___x_688_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v_P_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_ys_798_; lean_object* v_xs_799_; 
v_P_794_ = l_Lean_Syntax_getArg(v___x_475_, v___x_784_);
lean_dec(v___x_475_);
v___x_795_ = l_Lean_Syntax_getArgs(v___x_688_);
lean_dec(v___x_688_);
v___x_796_ = l_Array_extract___redArg(v___x_795_, v___x_474_, v___x_792_);
lean_dec_ref(v___x_795_);
v___x_797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_797_, 0, v___x_788_);
lean_ctor_set(v___x_797_, 1, v___x_787_);
lean_ctor_set(v___x_797_, 2, v___x_796_);
v_ys_798_ = l_Lean_Syntax_getArgs(v___x_789_);
lean_dec_ref(v___x_789_);
v_xs_799_ = l_Lean_Syntax_getArgs(v___x_797_);
lean_dec_ref(v___x_797_);
v_x_608_ = v_x_715_;
v_xs_609_ = v_xs_799_;
v_ty_610_ = v_ty_783_;
v_ys_611_ = v_ys_798_;
v_P_612_ = v_P_794_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_P_800_; lean_object* v_xs_801_; 
lean_dec(v___x_688_);
v_P_800_ = l_Lean_Syntax_getArg(v___x_475_, v___x_784_);
lean_dec(v___x_475_);
v_xs_801_ = l_Lean_Syntax_getArgs(v___x_789_);
lean_dec_ref(v___x_789_);
v_x_546_ = v_x_715_;
v_ty_547_ = v_ty_783_;
v_xs_548_ = v_xs_801_;
v_P_549_ = v_P_800_;
v___y_550_ = v_a_463_;
v___y_551_ = v_a_464_;
goto v___jp_545_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_unsigned_to_nat(2u);
v___x_803_ = l_Lean_Syntax_getArg(v___x_475_, v___x_802_);
v___x_804_ = l_Lean_Syntax_matchesNull(v___x_803_, v___x_473_);
if (v___x_804_ == 0)
{
lean_dec(v_x_683_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_P_811_; lean_object* v_xs_812_; 
v___x_805_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_806_ = l_Array_extract___redArg(v___x_805_, v___x_474_, v___x_681_);
lean_dec_ref(v___x_805_);
v___x_807_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_808_ = lean_box(2);
v___x_809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
lean_ctor_set(v___x_809_, 2, v___x_806_);
v___x_810_ = lean_unsigned_to_nat(4u);
v_P_811_ = l_Lean_Syntax_getArg(v___x_475_, v___x_810_);
lean_dec(v___x_475_);
v_xs_812_ = l_Lean_Syntax_getArgs(v___x_809_);
lean_dec_ref(v___x_809_);
v_x_490_ = v_x_683_;
v_xs_491_ = v_xs_812_;
v_P_492_ = v_P_811_;
v___y_493_ = v_a_463_;
v___y_494_ = v_a_464_;
goto v___jp_489_;
}
}
}
}
else
{
lean_object* v_x_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v_x_817_; lean_object* v_ty_818_; lean_object* v_P_819_; lean_object* v___y_820_; lean_object* v___y_821_; 
v_x_813_ = l_Lean_Syntax_getArg(v___x_679_, v___x_473_);
v___x_814_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62));
lean_inc(v_x_813_);
v___x_815_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_868_; lean_object* v_x_870_; lean_object* v_xs_871_; lean_object* v_ty_872_; lean_object* v_P_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v_____discr_935_; lean_object* v_____discr_936_; lean_object* v___y_937_; lean_object* v___y_938_; uint8_t v___x_1049_; 
v___x_868_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_813_);
v___x_1049_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_868_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_813_);
v___x_1051_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = l_Lean_Syntax_getNumArgs(v___x_679_);
v___x_1053_ = lean_nat_dec_le(v___x_474_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_P_1057_; 
v___x_1054_ = lean_unsigned_to_nat(2u);
v___x_1055_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1054_);
v___x_1056_ = lean_unsigned_to_nat(4u);
v_P_1057_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1056_);
lean_dec(v___x_475_);
if (v___x_1051_ == 0)
{
if (v___x_1049_ == 0)
{
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_unsigned_to_nat(3u);
v___x_1059_ = l_Lean_Syntax_getArg(v_x_813_, v___x_474_);
lean_inc(v___x_1059_);
v___x_1060_ = l_Lean_Syntax_matchesNull(v___x_1059_, v___x_474_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = l_Lean_Syntax_getNumArgs(v___x_1059_);
v___x_1062_ = lean_nat_dec_le(v___x_474_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec(v___x_1061_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v_x_1063_; uint8_t v___x_1064_; 
v_x_1063_ = l_Lean_Syntax_getArg(v___x_1059_, v___x_473_);
lean_inc(v_x_1063_);
v___x_1064_ = l_Lean_Syntax_isOfKind(v_x_1063_, v___x_1050_);
if (v___x_1064_ == 0)
{
lean_dec(v_x_1063_);
lean_dec(v___x_1061_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1054_);
lean_inc(v___x_1065_);
v___x_1066_ = l_Lean_Syntax_matchesNull(v___x_1065_, v___x_1054_);
if (v___x_1066_ == 0)
{
lean_dec(v___x_1065_);
lean_dec(v_x_1063_);
lean_dec(v___x_1061_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1058_);
lean_dec(v_x_813_);
v___x_1068_ = l_Lean_Syntax_matchesNull(v___x_1067_, v___x_473_);
if (v___x_1068_ == 0)
{
lean_dec(v___x_1065_);
lean_dec(v_x_1063_);
lean_dec(v___x_1061_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_473_);
if (v___x_1069_ == 0)
{
lean_dec(v___x_1065_);
lean_dec(v_x_1063_);
lean_dec(v___x_1061_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_ty_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_ys_1079_; lean_object* v_xs_1080_; 
v___x_1070_ = l_Lean_Syntax_getArgs(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1071_ = l_Array_extract___redArg(v___x_1070_, v___x_474_, v___x_1061_);
lean_dec_ref(v___x_1070_);
v_ty_1072_ = l_Lean_Syntax_getArg(v___x_1065_, v___x_474_);
lean_dec(v___x_1065_);
v___x_1073_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1074_ = lean_box(2);
v___x_1075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
lean_ctor_set(v___x_1075_, 2, v___x_1071_);
v___x_1076_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1077_ = l_Array_extract___redArg(v___x_1076_, v___x_474_, v___x_1052_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1074_);
lean_ctor_set(v___x_1078_, 1, v___x_1073_);
lean_ctor_set(v___x_1078_, 2, v___x_1077_);
v_ys_1079_ = l_Lean_Syntax_getArgs(v___x_1078_);
lean_dec_ref(v___x_1078_);
v_xs_1080_ = l_Lean_Syntax_getArgs(v___x_1075_);
lean_dec_ref(v___x_1075_);
v_x_608_ = v_x_1063_;
v_xs_609_ = v_xs_1080_;
v_ty_610_ = v_ty_1072_;
v_ys_611_ = v_ys_1079_;
v_P_612_ = v_P_1057_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_x_1081_; uint8_t v___x_1082_; 
v_x_1081_ = l_Lean_Syntax_getArg(v___x_1059_, v___x_473_);
lean_inc(v_x_1081_);
v___x_1082_ = l_Lean_Syntax_isOfKind(v_x_1081_, v___x_1050_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = l_Lean_Syntax_getNumArgs(v___x_1059_);
v___x_1084_ = lean_nat_dec_le(v___x_474_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec(v___x_1083_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1082_ == 0)
{
lean_dec(v___x_1083_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1054_);
lean_inc(v___x_1085_);
v___x_1086_ = l_Lean_Syntax_matchesNull(v___x_1085_, v___x_1054_);
if (v___x_1086_ == 0)
{
lean_dec(v___x_1085_);
lean_dec(v___x_1083_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1058_);
lean_dec(v_x_813_);
v___x_1088_ = l_Lean_Syntax_matchesNull(v___x_1087_, v___x_473_);
if (v___x_1088_ == 0)
{
lean_dec(v___x_1085_);
lean_dec(v___x_1083_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_473_);
if (v___x_1089_ == 0)
{
lean_dec(v___x_1085_);
lean_dec(v___x_1083_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_ty_1098_; lean_object* v_ys_1099_; lean_object* v_xs_1100_; 
v___x_1090_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1091_ = l_Array_extract___redArg(v___x_1090_, v___x_474_, v___x_1052_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1093_ = lean_box(2);
v___x_1094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___x_1092_);
lean_ctor_set(v___x_1094_, 2, v___x_1091_);
v___x_1095_ = l_Lean_Syntax_getArgs(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1096_ = l_Array_extract___redArg(v___x_1095_, v___x_474_, v___x_1083_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1093_);
lean_ctor_set(v___x_1097_, 1, v___x_1092_);
lean_ctor_set(v___x_1097_, 2, v___x_1096_);
v_ty_1098_ = l_Lean_Syntax_getArg(v___x_1085_, v___x_474_);
lean_dec(v___x_1085_);
v_ys_1099_ = l_Lean_Syntax_getArgs(v___x_1094_);
lean_dec_ref(v___x_1094_);
v_xs_1100_ = l_Lean_Syntax_getArgs(v___x_1097_);
lean_dec_ref(v___x_1097_);
v_x_608_ = v_x_1081_;
v_xs_609_ = v_xs_1100_;
v_ty_610_ = v_ty_1098_;
v_ys_611_ = v_ys_1099_;
v_P_612_ = v_P_1057_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1054_);
lean_inc(v___x_1101_);
v___x_1102_ = l_Lean_Syntax_matchesNull(v___x_1101_, v___x_1054_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = l_Lean_Syntax_getNumArgs(v___x_1059_);
v___x_1104_ = lean_nat_dec_le(v___x_474_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec(v___x_1103_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1082_ == 0)
{
lean_dec(v___x_1103_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1102_ == 0)
{
lean_dec(v___x_1103_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1058_);
lean_dec(v_x_813_);
v___x_1106_ = l_Lean_Syntax_matchesNull(v___x_1105_, v___x_473_);
if (v___x_1106_ == 0)
{
lean_dec(v___x_1103_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_473_);
if (v___x_1107_ == 0)
{
lean_dec(v___x_1103_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_ty_1116_; lean_object* v_ys_1117_; lean_object* v_xs_1118_; 
v___x_1108_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1109_ = l_Array_extract___redArg(v___x_1108_, v___x_474_, v___x_1052_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1111_ = lean_box(2);
v___x_1112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___x_1110_);
lean_ctor_set(v___x_1112_, 2, v___x_1109_);
v___x_1113_ = l_Lean_Syntax_getArgs(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1114_ = l_Array_extract___redArg(v___x_1113_, v___x_474_, v___x_1103_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1111_);
lean_ctor_set(v___x_1115_, 1, v___x_1110_);
lean_ctor_set(v___x_1115_, 2, v___x_1114_);
v_ty_1116_ = l_Lean_Syntax_getArg(v___x_1101_, v___x_474_);
lean_dec(v___x_1101_);
v_ys_1117_ = l_Lean_Syntax_getArgs(v___x_1112_);
lean_dec_ref(v___x_1112_);
v_xs_1118_ = l_Lean_Syntax_getArgs(v___x_1115_);
lean_dec_ref(v___x_1115_);
v_x_608_ = v_x_1081_;
v_xs_609_ = v_xs_1118_;
v_ty_610_ = v_ty_1116_;
v_ys_611_ = v_ys_1117_;
v_P_612_ = v_P_1057_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1058_);
lean_dec(v_x_813_);
v___x_1120_ = l_Lean_Syntax_matchesNull(v___x_1119_, v___x_473_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = l_Lean_Syntax_getNumArgs(v___x_1059_);
v___x_1122_ = lean_nat_dec_le(v___x_474_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_dec(v___x_1121_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1082_ == 0)
{
lean_dec(v___x_1121_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1102_ == 0)
{
lean_dec(v___x_1121_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1120_ == 0)
{
lean_dec(v___x_1121_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1055_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
uint8_t v___x_1123_; 
v___x_1123_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_473_);
if (v___x_1123_ == 0)
{
lean_dec(v___x_1121_);
lean_dec(v___x_1101_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec(v___x_1052_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_ty_1132_; lean_object* v_ys_1133_; lean_object* v_xs_1134_; 
v___x_1124_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1125_ = l_Array_extract___redArg(v___x_1124_, v___x_474_, v___x_1052_);
lean_dec_ref(v___x_1124_);
v___x_1126_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1127_ = lean_box(2);
v___x_1128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1126_);
lean_ctor_set(v___x_1128_, 2, v___x_1125_);
v___x_1129_ = l_Lean_Syntax_getArgs(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1130_ = l_Array_extract___redArg(v___x_1129_, v___x_474_, v___x_1121_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1127_);
lean_ctor_set(v___x_1131_, 1, v___x_1126_);
lean_ctor_set(v___x_1131_, 2, v___x_1130_);
v_ty_1132_ = l_Lean_Syntax_getArg(v___x_1101_, v___x_474_);
lean_dec(v___x_1101_);
v_ys_1133_ = l_Lean_Syntax_getArgs(v___x_1128_);
lean_dec_ref(v___x_1128_);
v_xs_1134_ = l_Lean_Syntax_getArgs(v___x_1131_);
lean_dec_ref(v___x_1131_);
v_x_608_ = v_x_1081_;
v_xs_609_ = v_xs_1134_;
v_ty_610_ = v_ty_1132_;
v_ys_611_ = v_ys_1133_;
v_P_612_ = v_P_1057_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_ty_1135_ = l_Lean_Syntax_getArg(v___x_1101_, v___x_474_);
lean_dec(v___x_1101_);
v___x_1136_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1137_ = l_Array_extract___redArg(v___x_1136_, v___x_474_, v___x_1052_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1139_ = lean_box(2);
v___x_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
lean_ctor_set(v___x_1140_, 2, v___x_1137_);
v___x_1141_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_473_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = l_Lean_Syntax_getNumArgs(v___x_1059_);
v___x_1143_ = lean_nat_dec_le(v___x_474_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_dec(v___x_1142_);
lean_dec_ref(v___x_1140_);
lean_dec(v_ty_1135_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1082_ == 0)
{
lean_dec(v___x_1142_);
lean_dec_ref(v___x_1140_);
lean_dec(v_ty_1135_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1102_ == 0)
{
lean_dec(v___x_1142_);
lean_dec_ref(v___x_1140_);
lean_dec(v_ty_1135_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1120_ == 0)
{
lean_dec(v___x_1142_);
lean_dec_ref(v___x_1140_);
lean_dec(v_ty_1135_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1141_ == 0)
{
lean_dec(v___x_1142_);
lean_dec_ref(v___x_1140_);
lean_dec(v_ty_1135_);
lean_dec(v_x_1081_);
lean_dec(v___x_1059_);
lean_dec(v_P_1057_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_ys_1147_; lean_object* v_xs_1148_; 
v___x_1144_ = l_Lean_Syntax_getArgs(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1145_ = l_Array_extract___redArg(v___x_1144_, v___x_474_, v___x_1142_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1139_);
lean_ctor_set(v___x_1146_, 1, v___x_1138_);
lean_ctor_set(v___x_1146_, 2, v___x_1145_);
v_ys_1147_ = l_Lean_Syntax_getArgs(v___x_1140_);
lean_dec_ref(v___x_1140_);
v_xs_1148_ = l_Lean_Syntax_getArgs(v___x_1146_);
lean_dec_ref(v___x_1146_);
v_x_608_ = v_x_1081_;
v_xs_609_ = v_xs_1148_;
v_ty_610_ = v_ty_1135_;
v_ys_611_ = v_ys_1147_;
v_P_612_ = v_P_1057_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1149_; 
lean_dec(v___x_1059_);
v_xs_1149_ = l_Lean_Syntax_getArgs(v___x_1140_);
lean_dec_ref(v___x_1140_);
v_x_546_ = v_x_1081_;
v_ty_547_ = v_ty_1135_;
v_xs_548_ = v_xs_1149_;
v_P_549_ = v_P_1057_;
v___y_550_ = v_a_463_;
v___y_551_ = v_a_464_;
goto v___jp_545_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___x_473_);
if (v___x_1150_ == 0)
{
lean_dec(v_P_1057_);
lean_dec(v___x_1052_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_xs_1156_; 
v___x_1151_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1152_ = l_Array_extract___redArg(v___x_1151_, v___x_474_, v___x_1052_);
lean_dec_ref(v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1154_ = lean_box(2);
v___x_1155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
lean_ctor_set(v___x_1155_, 2, v___x_1152_);
v_xs_1156_ = l_Lean_Syntax_getArgs(v___x_1155_);
lean_dec_ref(v___x_1155_);
v_x_490_ = v_x_813_;
v_xs_491_ = v_xs_1156_;
v_P_492_ = v_P_1057_;
v___y_493_ = v_a_463_;
v___y_494_ = v_a_464_;
goto v___jp_489_;
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(2u);
v___x_1158_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1157_);
v___x_1159_ = l_Lean_Syntax_matchesNull(v___x_1158_, v___x_473_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = l_Lean_Syntax_getNumArgs(v___x_679_);
v___x_1161_ = lean_nat_dec_le(v___x_474_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1162_; lean_object* v_P_1163_; 
v___x_1162_ = lean_unsigned_to_nat(4u);
v_P_1163_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1162_);
lean_dec(v___x_475_);
if (v___x_1051_ == 0)
{
if (v___x_1049_ == 0)
{
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_unsigned_to_nat(3u);
v___x_1165_ = l_Lean_Syntax_getArg(v_x_813_, v___x_474_);
lean_inc(v___x_1165_);
v___x_1166_ = l_Lean_Syntax_matchesNull(v___x_1165_, v___x_474_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = l_Lean_Syntax_getNumArgs(v___x_1165_);
v___x_1168_ = lean_nat_dec_le(v___x_474_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_dec(v___x_1167_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v_x_1169_; uint8_t v___x_1170_; 
v_x_1169_ = l_Lean_Syntax_getArg(v___x_1165_, v___x_473_);
lean_inc(v_x_1169_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v_x_1169_, v___x_1050_);
if (v___x_1170_ == 0)
{
lean_dec(v_x_1169_);
lean_dec(v___x_1167_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1157_);
lean_inc(v___x_1171_);
v___x_1172_ = l_Lean_Syntax_matchesNull(v___x_1171_, v___x_1157_);
if (v___x_1172_ == 0)
{
lean_dec(v___x_1171_);
lean_dec(v_x_1169_);
lean_dec(v___x_1167_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1164_);
lean_dec(v_x_813_);
v___x_1174_ = l_Lean_Syntax_matchesNull(v___x_1173_, v___x_473_);
if (v___x_1174_ == 0)
{
lean_dec(v___x_1171_);
lean_dec(v_x_1169_);
lean_dec(v___x_1167_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1159_ == 0)
{
lean_dec(v___x_1171_);
lean_dec(v_x_1169_);
lean_dec(v___x_1167_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_ty_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_ys_1184_; lean_object* v_xs_1185_; 
v___x_1175_ = l_Lean_Syntax_getArgs(v___x_1165_);
lean_dec(v___x_1165_);
v___x_1176_ = l_Array_extract___redArg(v___x_1175_, v___x_474_, v___x_1167_);
lean_dec_ref(v___x_1175_);
v_ty_1177_ = l_Lean_Syntax_getArg(v___x_1171_, v___x_474_);
lean_dec(v___x_1171_);
v___x_1178_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1179_ = lean_box(2);
v___x_1180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1178_);
lean_ctor_set(v___x_1180_, 2, v___x_1176_);
v___x_1181_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1182_ = l_Array_extract___redArg(v___x_1181_, v___x_474_, v___x_1160_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1179_);
lean_ctor_set(v___x_1183_, 1, v___x_1178_);
lean_ctor_set(v___x_1183_, 2, v___x_1182_);
v_ys_1184_ = l_Lean_Syntax_getArgs(v___x_1183_);
lean_dec_ref(v___x_1183_);
v_xs_1185_ = l_Lean_Syntax_getArgs(v___x_1180_);
lean_dec_ref(v___x_1180_);
v_x_608_ = v_x_1169_;
v_xs_609_ = v_xs_1185_;
v_ty_610_ = v_ty_1177_;
v_ys_611_ = v_ys_1184_;
v_P_612_ = v_P_1163_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_x_1186_; uint8_t v___x_1187_; 
v_x_1186_ = l_Lean_Syntax_getArg(v___x_1165_, v___x_473_);
lean_inc(v_x_1186_);
v___x_1187_ = l_Lean_Syntax_isOfKind(v_x_1186_, v___x_1050_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = l_Lean_Syntax_getNumArgs(v___x_1165_);
v___x_1189_ = lean_nat_dec_le(v___x_474_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec(v___x_1188_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1187_ == 0)
{
lean_dec(v___x_1188_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1157_);
lean_inc(v___x_1190_);
v___x_1191_ = l_Lean_Syntax_matchesNull(v___x_1190_, v___x_1157_);
if (v___x_1191_ == 0)
{
lean_dec(v___x_1190_);
lean_dec(v___x_1188_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1164_);
lean_dec(v_x_813_);
v___x_1193_ = l_Lean_Syntax_matchesNull(v___x_1192_, v___x_473_);
if (v___x_1193_ == 0)
{
lean_dec(v___x_1190_);
lean_dec(v___x_1188_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1159_ == 0)
{
lean_dec(v___x_1190_);
lean_dec(v___x_1188_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_ty_1202_; lean_object* v_ys_1203_; lean_object* v_xs_1204_; 
v___x_1194_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1195_ = l_Array_extract___redArg(v___x_1194_, v___x_474_, v___x_1160_);
lean_dec_ref(v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1197_ = lean_box(2);
v___x_1198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1196_);
lean_ctor_set(v___x_1198_, 2, v___x_1195_);
v___x_1199_ = l_Lean_Syntax_getArgs(v___x_1165_);
lean_dec(v___x_1165_);
v___x_1200_ = l_Array_extract___redArg(v___x_1199_, v___x_474_, v___x_1188_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1197_);
lean_ctor_set(v___x_1201_, 1, v___x_1196_);
lean_ctor_set(v___x_1201_, 2, v___x_1200_);
v_ty_1202_ = l_Lean_Syntax_getArg(v___x_1190_, v___x_474_);
lean_dec(v___x_1190_);
v_ys_1203_ = l_Lean_Syntax_getArgs(v___x_1198_);
lean_dec_ref(v___x_1198_);
v_xs_1204_ = l_Lean_Syntax_getArgs(v___x_1201_);
lean_dec_ref(v___x_1201_);
v_x_608_ = v_x_1186_;
v_xs_609_ = v_xs_1204_;
v_ty_610_ = v_ty_1202_;
v_ys_611_ = v_ys_1203_;
v_P_612_ = v_P_1163_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1157_);
lean_inc(v___x_1205_);
v___x_1206_ = l_Lean_Syntax_matchesNull(v___x_1205_, v___x_1157_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = l_Lean_Syntax_getNumArgs(v___x_1165_);
v___x_1208_ = lean_nat_dec_le(v___x_474_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_dec(v___x_1207_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1187_ == 0)
{
lean_dec(v___x_1207_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1206_ == 0)
{
lean_dec(v___x_1207_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1164_);
lean_dec(v_x_813_);
v___x_1210_ = l_Lean_Syntax_matchesNull(v___x_1209_, v___x_473_);
if (v___x_1210_ == 0)
{
lean_dec(v___x_1207_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1159_ == 0)
{
lean_dec(v___x_1207_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_ty_1219_; lean_object* v_ys_1220_; lean_object* v_xs_1221_; 
v___x_1211_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1212_ = l_Array_extract___redArg(v___x_1211_, v___x_474_, v___x_1160_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1214_ = lean_box(2);
v___x_1215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
lean_ctor_set(v___x_1215_, 2, v___x_1212_);
v___x_1216_ = l_Lean_Syntax_getArgs(v___x_1165_);
lean_dec(v___x_1165_);
v___x_1217_ = l_Array_extract___redArg(v___x_1216_, v___x_474_, v___x_1207_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1214_);
lean_ctor_set(v___x_1218_, 1, v___x_1213_);
lean_ctor_set(v___x_1218_, 2, v___x_1217_);
v_ty_1219_ = l_Lean_Syntax_getArg(v___x_1205_, v___x_474_);
lean_dec(v___x_1205_);
v_ys_1220_ = l_Lean_Syntax_getArgs(v___x_1215_);
lean_dec_ref(v___x_1215_);
v_xs_1221_ = l_Lean_Syntax_getArgs(v___x_1218_);
lean_dec_ref(v___x_1218_);
v_x_608_ = v_x_1186_;
v_xs_609_ = v_xs_1221_;
v_ty_610_ = v_ty_1219_;
v_ys_611_ = v_ys_1220_;
v_P_612_ = v_P_1163_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1164_);
lean_dec(v_x_813_);
v___x_1223_ = l_Lean_Syntax_matchesNull(v___x_1222_, v___x_473_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = l_Lean_Syntax_getNumArgs(v___x_1165_);
v___x_1225_ = lean_nat_dec_le(v___x_474_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_dec(v___x_1224_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1187_ == 0)
{
lean_dec(v___x_1224_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1206_ == 0)
{
lean_dec(v___x_1224_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1223_ == 0)
{
lean_dec(v___x_1224_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1159_ == 0)
{
lean_dec(v___x_1224_);
lean_dec(v___x_1205_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_ty_1234_; lean_object* v_ys_1235_; lean_object* v_xs_1236_; 
v___x_1226_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1227_ = l_Array_extract___redArg(v___x_1226_, v___x_474_, v___x_1160_);
lean_dec_ref(v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1229_ = lean_box(2);
v___x_1230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1228_);
lean_ctor_set(v___x_1230_, 2, v___x_1227_);
v___x_1231_ = l_Lean_Syntax_getArgs(v___x_1165_);
lean_dec(v___x_1165_);
v___x_1232_ = l_Array_extract___redArg(v___x_1231_, v___x_474_, v___x_1224_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1229_);
lean_ctor_set(v___x_1233_, 1, v___x_1228_);
lean_ctor_set(v___x_1233_, 2, v___x_1232_);
v_ty_1234_ = l_Lean_Syntax_getArg(v___x_1205_, v___x_474_);
lean_dec(v___x_1205_);
v_ys_1235_ = l_Lean_Syntax_getArgs(v___x_1230_);
lean_dec_ref(v___x_1230_);
v_xs_1236_ = l_Lean_Syntax_getArgs(v___x_1233_);
lean_dec_ref(v___x_1233_);
v_x_608_ = v_x_1186_;
v_xs_609_ = v_xs_1236_;
v_ty_610_ = v_ty_1234_;
v_ys_611_ = v_ys_1235_;
v_P_612_ = v_P_1163_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_ty_1237_ = l_Lean_Syntax_getArg(v___x_1205_, v___x_474_);
lean_dec(v___x_1205_);
v___x_1238_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1239_ = l_Array_extract___redArg(v___x_1238_, v___x_474_, v___x_1160_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1241_ = lean_box(2);
v___x_1242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___x_1240_);
lean_ctor_set(v___x_1242_, 2, v___x_1239_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = l_Lean_Syntax_getNumArgs(v___x_1165_);
v___x_1244_ = lean_nat_dec_le(v___x_474_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v_ty_1237_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1187_ == 0)
{
lean_dec(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v_ty_1237_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1206_ == 0)
{
lean_dec(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v_ty_1237_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1223_ == 0)
{
lean_dec(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v_ty_1237_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1159_ == 0)
{
lean_dec(v___x_1243_);
lean_dec_ref(v___x_1242_);
lean_dec(v_ty_1237_);
lean_dec(v_x_1186_);
lean_dec(v___x_1165_);
lean_dec(v_P_1163_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_ys_1248_; lean_object* v_xs_1249_; 
v___x_1245_ = l_Lean_Syntax_getArgs(v___x_1165_);
lean_dec(v___x_1165_);
v___x_1246_ = l_Array_extract___redArg(v___x_1245_, v___x_474_, v___x_1243_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1241_);
lean_ctor_set(v___x_1247_, 1, v___x_1240_);
lean_ctor_set(v___x_1247_, 2, v___x_1246_);
v_ys_1248_ = l_Lean_Syntax_getArgs(v___x_1242_);
lean_dec_ref(v___x_1242_);
v_xs_1249_ = l_Lean_Syntax_getArgs(v___x_1247_);
lean_dec_ref(v___x_1247_);
v_x_608_ = v_x_1186_;
v_xs_609_ = v_xs_1249_;
v_ty_610_ = v_ty_1237_;
v_ys_611_ = v_ys_1248_;
v_P_612_ = v_P_1163_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1250_; 
lean_dec(v___x_1165_);
v_xs_1250_ = l_Lean_Syntax_getArgs(v___x_1242_);
lean_dec_ref(v___x_1242_);
v_x_546_ = v_x_1186_;
v_ty_547_ = v_ty_1237_;
v_xs_548_ = v_xs_1250_;
v_P_549_ = v_P_1163_;
v___y_550_ = v_a_463_;
v___y_551_ = v_a_464_;
goto v___jp_545_;
}
}
}
}
}
}
}
else
{
if (v___x_1159_ == 0)
{
lean_dec(v_P_1163_);
lean_dec(v___x_1160_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_xs_1256_; 
v___x_1251_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1252_ = l_Array_extract___redArg(v___x_1251_, v___x_474_, v___x_1160_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1254_ = lean_box(2);
v___x_1255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1253_);
lean_ctor_set(v___x_1255_, 2, v___x_1252_);
v_xs_1256_ = l_Lean_Syntax_getArgs(v___x_1255_);
lean_dec_ref(v___x_1255_);
v_x_490_ = v_x_813_;
v_xs_491_ = v_xs_1256_;
v_P_492_ = v_P_1163_;
v___y_493_ = v_a_463_;
v___y_494_ = v_a_464_;
goto v___jp_489_;
}
}
}
}
else
{
lean_object* v_quotContext_1257_; lean_object* v_currMacroScope_1258_; lean_object* v_ref_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v___x_679_);
v_quotContext_1257_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_1257_);
v_currMacroScope_1258_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_1258_);
v_ref_1259_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_1259_);
lean_dec_ref(v_a_463_);
v___x_1260_ = lean_unsigned_to_nat(4u);
v___x_1261_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1260_);
lean_dec(v___x_475_);
v___x_1262_ = l_Lean_SourceInfo_fromRef(v_ref_1259_, v___x_1049_);
lean_dec(v_ref_1259_);
v___x_1263_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1264_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1265_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_1258_);
lean_inc(v_quotContext_1257_);
v___x_1266_ = l_Lean_addMacroScope(v_quotContext_1257_, v___x_1265_, v_currMacroScope_1258_);
v___x_1267_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_1262_);
v___x_1268_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1262_);
lean_ctor_set(v___x_1268_, 1, v___x_1264_);
lean_ctor_set(v___x_1268_, 2, v___x_1266_);
lean_ctor_set(v___x_1268_, 3, v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1270_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1271_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1272_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_1262_);
v___x_1273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1262_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1275_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Lean_addMacroScope(v_quotContext_1257_, v___x_1276_, v_currMacroScope_1258_);
v___x_1278_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_1262_);
v___x_1279_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1262_);
lean_ctor_set(v___x_1279_, 1, v___x_1275_);
lean_ctor_set(v___x_1279_, 2, v___x_1277_);
lean_ctor_set(v___x_1279_, 3, v___x_1278_);
lean_inc(v___x_1262_);
v___x_1280_ = l_Lean_Syntax_node1(v___x_1262_, v___x_1274_, v___x_1279_);
lean_inc(v___x_1262_);
v___x_1281_ = l_Lean_Syntax_node2(v___x_1262_, v___x_1271_, v___x_1273_, v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1283_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_1262_);
v___x_1284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1262_);
lean_ctor_set(v___x_1284_, 1, v___x_1282_);
v___x_1285_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_1262_);
v___x_1286_ = l_Lean_Syntax_node1(v___x_1262_, v___x_1269_, v_x_813_);
v___x_1287_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_1262_);
v___x_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1262_);
lean_ctor_set(v___x_1288_, 1, v___x_1269_);
lean_ctor_set(v___x_1288_, 2, v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_1262_);
v___x_1290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1262_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_1262_);
v___x_1292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1262_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_1262_);
v___x_1294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1262_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
lean_inc_ref(v___x_1294_);
lean_inc(v___x_1262_);
v___x_1295_ = l_Lean_Syntax_node3(v___x_1262_, v___x_469_, v___x_1292_, v___x_1261_, v___x_1294_);
lean_inc(v___x_1262_);
v___x_1296_ = l_Lean_Syntax_node4(v___x_1262_, v___x_1285_, v___x_1286_, v___x_1288_, v___x_1290_, v___x_1295_);
lean_inc(v___x_1262_);
v___x_1297_ = l_Lean_Syntax_node2(v___x_1262_, v___x_1283_, v___x_1284_, v___x_1296_);
lean_inc(v___x_1262_);
v___x_1298_ = l_Lean_Syntax_node3(v___x_1262_, v___x_1270_, v___x_1281_, v___x_1297_, v___x_1294_);
lean_inc(v___x_1262_);
v___x_1299_ = l_Lean_Syntax_node1(v___x_1262_, v___x_1269_, v___x_1298_);
v___x_1300_ = l_Lean_Syntax_node2(v___x_1262_, v___x_1263_, v___x_1268_, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_a_464_);
return v___x_1301_;
}
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1302_ = l_Lean_Syntax_getArg(v_x_813_, v___x_474_);
v___x_1303_ = l_Lean_Syntax_getNumArgs(v___x_1302_);
v___x_1304_ = lean_nat_dec_le(v___x_474_, v___x_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; 
lean_inc(v___x_1302_);
v___x_1305_ = l_Lean_Syntax_matchesNull(v___x_1302_, v___x_474_);
if (v___x_1305_ == 0)
{
if (v___x_1304_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v___x_1306_ = lean_unsigned_to_nat(2u);
v___x_1307_ = lean_unsigned_to_nat(4u);
v___x_1308_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1306_);
v___x_1309_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1307_);
lean_dec(v___x_475_);
v_____discr_935_ = v___x_1308_;
v_____discr_936_ = v___x_1309_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v_x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_x_1310_ = l_Lean_Syntax_getArg(v___x_1302_, v___x_473_);
v___x_1311_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1310_);
v___x_1312_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v_x_1310_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v___x_1313_ = lean_unsigned_to_nat(2u);
v___x_1314_ = lean_unsigned_to_nat(4u);
v___x_1315_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1313_);
v___x_1316_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1314_);
lean_dec(v___x_475_);
v_____discr_935_ = v___x_1315_;
v_____discr_936_ = v___x_1316_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1317_ = lean_unsigned_to_nat(2u);
v___x_1318_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1317_);
lean_inc(v___x_1318_);
v___x_1319_ = l_Lean_Syntax_matchesNull(v___x_1318_, v___x_1317_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v___x_1318_);
lean_dec(v_x_1310_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v___x_1320_ = lean_unsigned_to_nat(4u);
v___x_1321_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1317_);
v___x_1322_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1320_);
lean_dec(v___x_475_);
v_____discr_935_ = v___x_1321_;
v_____discr_936_ = v___x_1322_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_unsigned_to_nat(3u);
v___x_1324_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1323_);
v___x_1325_ = l_Lean_Syntax_matchesNull(v___x_1324_, v___x_473_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v___x_1318_);
lean_dec(v_x_1310_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v___x_1326_ = lean_unsigned_to_nat(4u);
v___x_1327_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1317_);
v___x_1328_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1326_);
lean_dec(v___x_475_);
v_____discr_935_ = v___x_1327_;
v_____discr_936_ = v___x_1328_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(4u);
v___x_1330_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1317_);
lean_inc(v___x_1330_);
v___x_1331_ = l_Lean_Syntax_matchesNull(v___x_1330_, v___x_473_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec(v___x_1318_);
lean_dec(v_x_1310_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v___x_1332_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1329_);
lean_dec(v___x_475_);
v_____discr_935_ = v___x_1330_;
v_____discr_936_ = v___x_1332_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_ty_1338_; lean_object* v_P_1339_; lean_object* v_xs_1340_; 
lean_dec(v___x_1330_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1333_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1334_ = l_Array_extract___redArg(v___x_1333_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1336_ = lean_box(2);
v___x_1337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v___x_1334_);
v_ty_1338_ = l_Lean_Syntax_getArg(v___x_1318_, v___x_474_);
lean_dec(v___x_1318_);
v_P_1339_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1329_);
lean_dec(v___x_475_);
v_xs_1340_ = l_Lean_Syntax_getArgs(v___x_1337_);
lean_dec_ref(v___x_1337_);
v_x_870_ = v_x_1310_;
v_xs_871_ = v_xs_1340_;
v_ty_872_ = v_ty_1338_;
v_P_873_ = v_P_1339_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v_x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_x_1341_ = l_Lean_Syntax_getArg(v___x_1302_, v___x_473_);
v___x_1342_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1341_);
v___x_1343_ = l_Lean_Syntax_isOfKind(v_x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v_P_1347_; 
v___x_1344_ = lean_unsigned_to_nat(2u);
v___x_1345_ = lean_unsigned_to_nat(4u);
v___x_1346_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1344_);
v_P_1347_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1345_);
lean_dec(v___x_475_);
if (v___x_1304_ == 0)
{
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1346_;
v_____discr_936_ = v_P_1347_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1343_ == 0)
{
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1346_;
v_____discr_936_ = v_P_1347_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1344_);
lean_inc(v___x_1348_);
v___x_1349_ = l_Lean_Syntax_matchesNull(v___x_1348_, v___x_1344_);
if (v___x_1349_ == 0)
{
lean_dec(v___x_1348_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1346_;
v_____discr_936_ = v_P_1347_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_unsigned_to_nat(3u);
v___x_1351_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1350_);
v___x_1352_ = l_Lean_Syntax_matchesNull(v___x_1351_, v___x_473_);
if (v___x_1352_ == 0)
{
lean_dec(v___x_1348_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1346_;
v_____discr_936_ = v_P_1347_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1353_; 
lean_inc(v___x_1346_);
v___x_1353_ = l_Lean_Syntax_matchesNull(v___x_1346_, v___x_473_);
if (v___x_1353_ == 0)
{
lean_dec(v___x_1348_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1346_;
v_____discr_936_ = v_P_1347_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_ty_1359_; lean_object* v_xs_1360_; 
lean_dec(v___x_1346_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1354_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1355_ = l_Array_extract___redArg(v___x_1354_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1357_ = lean_box(2);
v___x_1358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
lean_ctor_set(v___x_1358_, 2, v___x_1355_);
v_ty_1359_ = l_Lean_Syntax_getArg(v___x_1348_, v___x_474_);
lean_dec(v___x_1348_);
v_xs_1360_ = l_Lean_Syntax_getArgs(v___x_1358_);
lean_dec_ref(v___x_1358_);
v_x_870_ = v_x_1341_;
v_xs_871_ = v_xs_1360_;
v_ty_872_ = v_ty_1359_;
v_P_873_ = v_P_1347_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_unsigned_to_nat(2u);
v___x_1362_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1361_);
lean_inc(v___x_1362_);
v___x_1363_ = l_Lean_Syntax_matchesNull(v___x_1362_, v___x_1361_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_P_1366_; 
v___x_1364_ = lean_unsigned_to_nat(4u);
v___x_1365_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1361_);
v_P_1366_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1364_);
lean_dec(v___x_475_);
if (v___x_1304_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1365_;
v_____discr_936_ = v_P_1366_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1343_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1365_;
v_____discr_936_ = v_P_1366_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1363_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1365_;
v_____discr_936_ = v_P_1366_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_unsigned_to_nat(3u);
v___x_1368_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1367_);
v___x_1369_ = l_Lean_Syntax_matchesNull(v___x_1368_, v___x_473_);
if (v___x_1369_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1365_;
v_____discr_936_ = v_P_1366_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1370_; 
lean_inc(v___x_1365_);
v___x_1370_ = l_Lean_Syntax_matchesNull(v___x_1365_, v___x_473_);
if (v___x_1370_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1365_;
v_____discr_936_ = v_P_1366_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_ty_1376_; lean_object* v_xs_1377_; 
lean_dec(v___x_1365_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1371_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1372_ = l_Array_extract___redArg(v___x_1371_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1374_ = lean_box(2);
v___x_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1373_);
lean_ctor_set(v___x_1375_, 2, v___x_1372_);
v_ty_1376_ = l_Lean_Syntax_getArg(v___x_1362_, v___x_474_);
lean_dec(v___x_1362_);
v_xs_1377_ = l_Lean_Syntax_getArgs(v___x_1375_);
lean_dec_ref(v___x_1375_);
v_x_870_ = v_x_1341_;
v_xs_871_ = v_xs_1377_;
v_ty_872_ = v_ty_1376_;
v_P_873_ = v_P_1366_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = lean_unsigned_to_nat(3u);
v___x_1379_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1378_);
v___x_1380_ = l_Lean_Syntax_matchesNull(v___x_1379_, v___x_473_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v_P_1383_; 
v___x_1381_ = lean_unsigned_to_nat(4u);
v___x_1382_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1361_);
v_P_1383_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1381_);
lean_dec(v___x_475_);
if (v___x_1304_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1382_;
v_____discr_936_ = v_P_1383_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1343_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1382_;
v_____discr_936_ = v_P_1383_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1363_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1382_;
v_____discr_936_ = v_P_1383_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1380_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1382_;
v_____discr_936_ = v_P_1383_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1384_; 
lean_inc(v___x_1382_);
v___x_1384_ = l_Lean_Syntax_matchesNull(v___x_1382_, v___x_473_);
if (v___x_1384_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1382_;
v_____discr_936_ = v_P_1383_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_ty_1390_; lean_object* v_xs_1391_; 
lean_dec(v___x_1382_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1385_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1386_ = l_Array_extract___redArg(v___x_1385_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1388_ = lean_box(2);
v___x_1389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___x_1387_);
lean_ctor_set(v___x_1389_, 2, v___x_1386_);
v_ty_1390_ = l_Lean_Syntax_getArg(v___x_1362_, v___x_474_);
lean_dec(v___x_1362_);
v_xs_1391_ = l_Lean_Syntax_getArgs(v___x_1389_);
lean_dec_ref(v___x_1389_);
v_x_870_ = v_x_1341_;
v_xs_871_ = v_xs_1391_;
v_ty_872_ = v_ty_1390_;
v_P_873_ = v_P_1383_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = lean_unsigned_to_nat(4u);
v___x_1393_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1361_);
lean_inc(v___x_1393_);
v___x_1394_ = l_Lean_Syntax_matchesNull(v___x_1393_, v___x_473_);
if (v___x_1394_ == 0)
{
lean_object* v_P_1395_; 
v_P_1395_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1392_);
lean_dec(v___x_475_);
if (v___x_1304_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1393_;
v_____discr_936_ = v_P_1395_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1343_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1393_;
v_____discr_936_ = v_P_1395_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1363_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1393_;
v_____discr_936_ = v_P_1395_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1380_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1393_;
v_____discr_936_ = v_P_1395_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1394_ == 0)
{
lean_dec(v___x_1362_);
lean_dec(v_x_1341_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1393_;
v_____discr_936_ = v_P_1395_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_ty_1401_; lean_object* v_xs_1402_; 
lean_dec(v___x_1393_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1396_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1397_ = l_Array_extract___redArg(v___x_1396_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1399_ = lean_box(2);
v___x_1400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1398_);
lean_ctor_set(v___x_1400_, 2, v___x_1397_);
v_ty_1401_ = l_Lean_Syntax_getArg(v___x_1362_, v___x_474_);
lean_dec(v___x_1362_);
v_xs_1402_ = l_Lean_Syntax_getArgs(v___x_1400_);
lean_dec_ref(v___x_1400_);
v_x_870_ = v_x_1341_;
v_xs_871_ = v_xs_1402_;
v_ty_872_ = v_ty_1401_;
v_P_873_ = v_P_1395_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1403_; lean_object* v_P_1404_; 
lean_dec(v___x_1393_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_ty_1403_ = l_Lean_Syntax_getArg(v___x_1362_, v___x_474_);
lean_dec(v___x_1362_);
v_P_1404_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1392_);
lean_dec(v___x_475_);
v_x_817_ = v_x_1341_;
v_ty_818_ = v_ty_1403_;
v_P_819_ = v_P_1404_;
v___y_820_ = v_a_463_;
v___y_821_ = v_a_464_;
goto v___jp_816_;
}
}
}
}
}
}
else
{
lean_object* v_x_1405_; uint8_t v___x_1406_; 
v_x_1405_ = l_Lean_Syntax_getArg(v___x_1302_, v___x_473_);
lean_inc(v_x_1405_);
v___x_1406_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_814_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_P_1413_; uint8_t v___x_1414_; 
v___x_1407_ = lean_unsigned_to_nat(2u);
v___x_1408_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1407_);
v___x_1409_ = lean_unsigned_to_nat(3u);
v___x_1410_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1409_);
v___x_1411_ = lean_unsigned_to_nat(4u);
v___x_1412_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1407_);
v_P_1413_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1411_);
lean_dec(v___x_475_);
lean_inc(v___x_1302_);
v___x_1414_ = l_Lean_Syntax_matchesNull(v___x_1302_, v___x_474_);
if (v___x_1414_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1416_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1417_; 
lean_inc(v___x_1408_);
v___x_1417_ = l_Lean_Syntax_matchesNull(v___x_1408_, v___x_1407_);
if (v___x_1417_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1418_; 
v___x_1418_ = l_Lean_Syntax_matchesNull(v___x_1410_, v___x_473_);
if (v___x_1418_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1419_; 
lean_inc(v___x_1412_);
v___x_1419_ = l_Lean_Syntax_matchesNull(v___x_1412_, v___x_473_);
if (v___x_1419_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_ty_1425_; lean_object* v_xs_1426_; 
lean_dec(v___x_1412_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1420_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1421_ = l_Array_extract___redArg(v___x_1420_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1420_);
v___x_1422_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1423_ = lean_box(2);
v___x_1424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___x_1422_);
lean_ctor_set(v___x_1424_, 2, v___x_1421_);
v_ty_1425_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_474_);
lean_dec(v___x_1408_);
v_xs_1426_ = l_Lean_Syntax_getArgs(v___x_1424_);
lean_dec_ref(v___x_1424_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1426_;
v_ty_872_ = v_ty_1425_;
v_P_873_ = v_P_1413_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1428_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1427_);
if (v___x_1428_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1428_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1429_; 
lean_inc(v___x_1408_);
v___x_1429_ = l_Lean_Syntax_matchesNull(v___x_1408_, v___x_1407_);
if (v___x_1429_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = l_Lean_Syntax_matchesNull(v___x_1410_, v___x_473_);
if (v___x_1430_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1431_; 
lean_inc(v___x_1412_);
v___x_1431_ = l_Lean_Syntax_matchesNull(v___x_1412_, v___x_473_);
if (v___x_1431_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_ty_1437_; lean_object* v_xs_1438_; 
lean_dec(v___x_1412_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1432_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1433_ = l_Array_extract___redArg(v___x_1432_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1435_ = lean_box(2);
v___x_1436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___x_1434_);
lean_ctor_set(v___x_1436_, 2, v___x_1433_);
v_ty_1437_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_474_);
lean_dec(v___x_1408_);
v_xs_1438_ = l_Lean_Syntax_getArgs(v___x_1436_);
lean_dec_ref(v___x_1436_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1438_;
v_ty_872_ = v_ty_1437_;
v_P_873_ = v_P_1413_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
uint8_t v___x_1439_; 
lean_inc(v___x_1408_);
v___x_1439_ = l_Lean_Syntax_matchesNull(v___x_1408_, v___x_1407_);
if (v___x_1439_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1428_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1439_ == 0)
{
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1440_; 
v___x_1440_ = l_Lean_Syntax_matchesNull(v___x_1410_, v___x_473_);
if (v___x_1440_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1441_; 
lean_inc(v___x_1412_);
v___x_1441_ = l_Lean_Syntax_matchesNull(v___x_1412_, v___x_473_);
if (v___x_1441_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_ty_1447_; lean_object* v_xs_1448_; 
lean_dec(v___x_1412_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1442_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1443_ = l_Array_extract___redArg(v___x_1442_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1445_ = lean_box(2);
v___x_1446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___x_1444_);
lean_ctor_set(v___x_1446_, 2, v___x_1443_);
v_ty_1447_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_474_);
lean_dec(v___x_1408_);
v_xs_1448_ = l_Lean_Syntax_getArgs(v___x_1446_);
lean_dec_ref(v___x_1446_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1448_;
v_ty_872_ = v_ty_1447_;
v_P_873_ = v_P_1413_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = l_Lean_Syntax_matchesNull(v___x_1410_, v___x_473_);
if (v___x_1449_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1428_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1439_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1449_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1450_; 
lean_inc(v___x_1412_);
v___x_1450_ = l_Lean_Syntax_matchesNull(v___x_1412_, v___x_473_);
if (v___x_1450_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_ty_1456_; lean_object* v_xs_1457_; 
lean_dec(v___x_1412_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1451_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1452_ = l_Array_extract___redArg(v___x_1451_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1454_ = lean_box(2);
v___x_1455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1453_);
lean_ctor_set(v___x_1455_, 2, v___x_1452_);
v_ty_1456_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_474_);
lean_dec(v___x_1408_);
v_xs_1457_ = l_Lean_Syntax_getArgs(v___x_1455_);
lean_dec_ref(v___x_1455_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1457_;
v_ty_872_ = v_ty_1456_;
v_P_873_ = v_P_1413_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
uint8_t v___x_1458_; 
lean_inc(v___x_1412_);
v___x_1458_ = l_Lean_Syntax_matchesNull(v___x_1412_, v___x_473_);
if (v___x_1458_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1428_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1439_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1449_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1458_ == 0)
{
lean_dec(v___x_1408_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1412_;
v_____discr_936_ = v_P_1413_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_ty_1464_; lean_object* v_xs_1465_; 
lean_dec(v___x_1412_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1459_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1460_ = l_Array_extract___redArg(v___x_1459_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1462_ = lean_box(2);
v___x_1463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v___x_1460_);
v_ty_1464_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_474_);
lean_dec(v___x_1408_);
v_xs_1465_ = l_Lean_Syntax_getArgs(v___x_1463_);
lean_dec_ref(v___x_1463_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1465_;
v_ty_872_ = v_ty_1464_;
v_P_873_ = v_P_1413_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1466_; 
lean_dec(v___x_1412_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_ty_1466_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_474_);
lean_dec(v___x_1408_);
v_x_817_ = v_x_1405_;
v_ty_818_ = v_ty_1466_;
v_P_819_ = v_P_1413_;
v___y_820_ = v_a_463_;
v___y_821_ = v_a_464_;
goto v___jp_816_;
}
}
}
}
}
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1467_);
lean_inc(v___x_1468_);
v___x_1469_ = l_Lean_Syntax_matchesNull(v___x_1468_, v___x_1467_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v_P_1474_; uint8_t v___x_1475_; 
v___x_1470_ = lean_unsigned_to_nat(3u);
v___x_1471_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1470_);
v___x_1472_ = lean_unsigned_to_nat(4u);
v___x_1473_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1467_);
v_P_1474_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1472_);
lean_dec(v___x_475_);
lean_inc(v___x_1302_);
v___x_1475_ = l_Lean_Syntax_matchesNull(v___x_1302_, v___x_474_);
if (v___x_1475_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1477_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1478_; 
v___x_1478_ = l_Lean_Syntax_matchesNull(v___x_1471_, v___x_473_);
if (v___x_1478_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1479_; 
lean_inc(v___x_1473_);
v___x_1479_ = l_Lean_Syntax_matchesNull(v___x_1473_, v___x_473_);
if (v___x_1479_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_ty_1485_; lean_object* v_xs_1486_; 
lean_dec(v___x_1473_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1480_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1481_ = l_Array_extract___redArg(v___x_1480_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1480_);
v___x_1482_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1483_ = lean_box(2);
v___x_1484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v___x_1481_);
v_ty_1485_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1486_ = l_Lean_Syntax_getArgs(v___x_1484_);
lean_dec_ref(v___x_1484_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1486_;
v_ty_872_ = v_ty_1485_;
v_P_873_ = v_P_1474_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1488_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1487_);
if (v___x_1488_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1488_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Lean_Syntax_matchesNull(v___x_1471_, v___x_473_);
if (v___x_1489_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1490_; 
lean_inc(v___x_1473_);
v___x_1490_ = l_Lean_Syntax_matchesNull(v___x_1473_, v___x_473_);
if (v___x_1490_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_ty_1496_; lean_object* v_xs_1497_; 
lean_dec(v___x_1473_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1491_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1492_ = l_Array_extract___redArg(v___x_1491_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1494_ = lean_box(2);
v___x_1495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1493_);
lean_ctor_set(v___x_1495_, 2, v___x_1492_);
v_ty_1496_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1497_ = l_Lean_Syntax_getArgs(v___x_1495_);
lean_dec_ref(v___x_1495_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1497_;
v_ty_872_ = v_ty_1496_;
v_P_873_ = v_P_1474_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
if (v___x_1469_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1488_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_Syntax_matchesNull(v___x_1471_, v___x_473_);
if (v___x_1498_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1499_; 
lean_inc(v___x_1473_);
v___x_1499_ = l_Lean_Syntax_matchesNull(v___x_1473_, v___x_473_);
if (v___x_1499_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_ty_1505_; lean_object* v_xs_1506_; 
lean_dec(v___x_1473_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1500_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1501_ = l_Array_extract___redArg(v___x_1500_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1500_);
v___x_1502_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1503_ = lean_box(2);
v___x_1504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
lean_ctor_set(v___x_1504_, 2, v___x_1501_);
v_ty_1505_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1506_ = l_Lean_Syntax_getArgs(v___x_1504_);
lean_dec_ref(v___x_1504_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1506_;
v_ty_872_ = v_ty_1505_;
v_P_873_ = v_P_1474_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = l_Lean_Syntax_matchesNull(v___x_1471_, v___x_473_);
if (v___x_1507_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1488_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1507_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1508_; 
lean_inc(v___x_1473_);
v___x_1508_ = l_Lean_Syntax_matchesNull(v___x_1473_, v___x_473_);
if (v___x_1508_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_ty_1514_; lean_object* v_xs_1515_; 
lean_dec(v___x_1473_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1509_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1510_ = l_Array_extract___redArg(v___x_1509_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1512_ = lean_box(2);
v___x_1513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v___x_1511_);
lean_ctor_set(v___x_1513_, 2, v___x_1510_);
v_ty_1514_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1515_ = l_Lean_Syntax_getArgs(v___x_1513_);
lean_dec_ref(v___x_1513_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1515_;
v_ty_872_ = v_ty_1514_;
v_P_873_ = v_P_1474_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
uint8_t v___x_1516_; 
lean_inc(v___x_1473_);
v___x_1516_ = l_Lean_Syntax_matchesNull(v___x_1473_, v___x_473_);
if (v___x_1516_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1488_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1507_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1516_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1473_;
v_____discr_936_ = v_P_1474_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_ty_1522_; lean_object* v_xs_1523_; 
lean_dec(v___x_1473_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1517_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1518_ = l_Array_extract___redArg(v___x_1517_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1520_ = lean_box(2);
v___x_1521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
lean_ctor_set(v___x_1521_, 2, v___x_1518_);
v_ty_1522_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1523_ = l_Lean_Syntax_getArgs(v___x_1521_);
lean_dec_ref(v___x_1521_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1523_;
v_ty_872_ = v_ty_1522_;
v_P_873_ = v_P_1474_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1524_; 
lean_dec(v___x_1473_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_ty_1524_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_x_817_ = v_x_1405_;
v_ty_818_ = v_ty_1524_;
v_P_819_ = v_P_1474_;
v___y_820_ = v_a_463_;
v___y_821_ = v_a_464_;
goto v___jp_816_;
}
}
}
}
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = lean_unsigned_to_nat(3u);
v___x_1526_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1525_);
v___x_1527_ = l_Lean_Syntax_matchesNull(v___x_1526_, v___x_473_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_P_1530_; uint8_t v___x_1531_; 
v___x_1528_ = lean_unsigned_to_nat(4u);
v___x_1529_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1467_);
v_P_1530_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1528_);
lean_dec(v___x_475_);
lean_inc(v___x_1302_);
v___x_1531_ = l_Lean_Syntax_matchesNull(v___x_1302_, v___x_474_);
if (v___x_1531_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1533_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1534_; 
lean_inc(v___x_1529_);
v___x_1534_ = l_Lean_Syntax_matchesNull(v___x_1529_, v___x_473_);
if (v___x_1534_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_ty_1540_; lean_object* v_xs_1541_; 
lean_dec(v___x_1529_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1535_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1536_ = l_Array_extract___redArg(v___x_1535_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1538_ = lean_box(2);
v___x_1539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1537_);
lean_ctor_set(v___x_1539_, 2, v___x_1536_);
v_ty_1540_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1541_ = l_Lean_Syntax_getArgs(v___x_1539_);
lean_dec_ref(v___x_1539_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1541_;
v_ty_872_ = v_ty_1540_;
v_P_873_ = v_P_1530_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1543_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1542_);
if (v___x_1543_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1543_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1544_; 
lean_inc(v___x_1529_);
v___x_1544_ = l_Lean_Syntax_matchesNull(v___x_1529_, v___x_473_);
if (v___x_1544_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_ty_1550_; lean_object* v_xs_1551_; 
lean_dec(v___x_1529_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1545_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1546_ = l_Array_extract___redArg(v___x_1545_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1548_ = lean_box(2);
v___x_1549_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1547_);
lean_ctor_set(v___x_1549_, 2, v___x_1546_);
v_ty_1550_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1551_ = l_Lean_Syntax_getArgs(v___x_1549_);
lean_dec_ref(v___x_1549_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1551_;
v_ty_872_ = v_ty_1550_;
v_P_873_ = v_P_1530_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
if (v___x_1469_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1543_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1552_; 
lean_inc(v___x_1529_);
v___x_1552_ = l_Lean_Syntax_matchesNull(v___x_1529_, v___x_473_);
if (v___x_1552_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_ty_1558_; lean_object* v_xs_1559_; 
lean_dec(v___x_1529_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1553_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1554_ = l_Array_extract___redArg(v___x_1553_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1556_ = lean_box(2);
v___x_1557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___x_1555_);
lean_ctor_set(v___x_1557_, 2, v___x_1554_);
v_ty_1558_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1559_ = l_Lean_Syntax_getArgs(v___x_1557_);
lean_dec_ref(v___x_1557_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1559_;
v_ty_872_ = v_ty_1558_;
v_P_873_ = v_P_1530_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
if (v___x_1527_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1543_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
uint8_t v___x_1560_; 
lean_inc(v___x_1529_);
v___x_1560_ = l_Lean_Syntax_matchesNull(v___x_1529_, v___x_473_);
if (v___x_1560_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v_ty_1566_; lean_object* v_xs_1567_; 
lean_dec(v___x_1529_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1561_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1562_ = l_Array_extract___redArg(v___x_1561_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1564_ = lean_box(2);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1563_);
lean_ctor_set(v___x_1565_, 2, v___x_1562_);
v_ty_1566_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1567_ = l_Lean_Syntax_getArgs(v___x_1565_);
lean_dec_ref(v___x_1565_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1567_;
v_ty_872_ = v_ty_1566_;
v_P_873_ = v_P_1530_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
uint8_t v___x_1568_; 
lean_inc(v___x_1529_);
v___x_1568_ = l_Lean_Syntax_matchesNull(v___x_1529_, v___x_473_);
if (v___x_1568_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1543_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1568_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1529_;
v_____discr_936_ = v_P_1530_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_ty_1574_; lean_object* v_xs_1575_; 
lean_dec(v___x_1529_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1569_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1570_ = l_Array_extract___redArg(v___x_1569_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1572_ = lean_box(2);
v___x_1573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___x_1571_);
lean_ctor_set(v___x_1573_, 2, v___x_1570_);
v_ty_1574_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1575_ = l_Lean_Syntax_getArgs(v___x_1573_);
lean_dec_ref(v___x_1573_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1575_;
v_ty_872_ = v_ty_1574_;
v_P_873_ = v_P_1530_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1576_; 
lean_dec(v___x_1529_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_ty_1576_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_x_817_ = v_x_1405_;
v_ty_818_ = v_ty_1576_;
v_P_819_ = v_P_1530_;
v___y_820_ = v_a_463_;
v___y_821_ = v_a_464_;
goto v___jp_816_;
}
}
}
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1577_ = lean_unsigned_to_nat(4u);
v___x_1578_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1467_);
lean_inc(v___x_1578_);
v___x_1579_ = l_Lean_Syntax_matchesNull(v___x_1578_, v___x_473_);
if (v___x_1579_ == 0)
{
lean_object* v_P_1580_; uint8_t v___x_1581_; 
v_P_1580_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1577_);
lean_dec(v___x_475_);
lean_inc(v___x_1302_);
v___x_1581_ = l_Lean_Syntax_matchesNull(v___x_1302_, v___x_474_);
if (v___x_1581_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1583_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1579_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_ty_1589_; lean_object* v_xs_1590_; 
lean_dec(v___x_1578_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1584_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1585_ = l_Array_extract___redArg(v___x_1584_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1587_ = lean_box(2);
v___x_1588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v___x_1586_);
lean_ctor_set(v___x_1588_, 2, v___x_1585_);
v_ty_1589_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1590_ = l_Lean_Syntax_getArgs(v___x_1588_);
lean_dec_ref(v___x_1588_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1590_;
v_ty_872_ = v_ty_1589_;
v_P_873_ = v_P_1580_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1405_);
v___x_1592_ = l_Lean_Syntax_isOfKind(v_x_1405_, v___x_1591_);
if (v___x_1592_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1592_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1579_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_ty_1598_; lean_object* v_xs_1599_; 
lean_dec(v___x_1578_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1593_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1594_ = l_Array_extract___redArg(v___x_1593_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1596_ = lean_box(2);
v___x_1597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v___x_1595_);
lean_ctor_set(v___x_1597_, 2, v___x_1594_);
v_ty_1598_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1599_ = l_Lean_Syntax_getArgs(v___x_1597_);
lean_dec_ref(v___x_1597_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1599_;
v_ty_872_ = v_ty_1598_;
v_P_873_ = v_P_1580_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
if (v___x_1469_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1592_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1579_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_ty_1605_; lean_object* v_xs_1606_; 
lean_dec(v___x_1578_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1600_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1601_ = l_Array_extract___redArg(v___x_1600_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1603_ = lean_box(2);
v___x_1604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___x_1602_);
lean_ctor_set(v___x_1604_, 2, v___x_1601_);
v_ty_1605_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1606_ = l_Lean_Syntax_getArgs(v___x_1604_);
lean_dec_ref(v___x_1604_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1606_;
v_ty_872_ = v_ty_1605_;
v_P_873_ = v_P_1580_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
if (v___x_1527_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1592_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1579_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v_ty_1612_; lean_object* v_xs_1613_; 
lean_dec(v___x_1578_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1607_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1608_ = l_Array_extract___redArg(v___x_1607_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1610_ = lean_box(2);
v___x_1611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v___x_1609_);
lean_ctor_set(v___x_1611_, 2, v___x_1608_);
v_ty_1612_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1613_ = l_Lean_Syntax_getArgs(v___x_1611_);
lean_dec_ref(v___x_1611_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1613_;
v_ty_872_ = v_ty_1612_;
v_P_873_ = v_P_1580_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
if (v___x_1579_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1592_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1527_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
if (v___x_1579_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v_x_1405_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
v_____discr_935_ = v___x_1578_;
v_____discr_936_ = v_P_1580_;
v___y_937_ = v_a_463_;
v___y_938_ = v_a_464_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_ty_1619_; lean_object* v_xs_1620_; 
lean_dec(v___x_1578_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___x_1614_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1615_ = l_Array_extract___redArg(v___x_1614_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1617_ = lean_box(2);
v___x_1618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___x_1616_);
lean_ctor_set(v___x_1618_, 2, v___x_1615_);
v_ty_1619_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_xs_1620_ = l_Lean_Syntax_getArgs(v___x_1618_);
lean_dec_ref(v___x_1618_);
v_x_870_ = v_x_1405_;
v_xs_871_ = v_xs_1620_;
v_ty_872_ = v_ty_1619_;
v_P_873_ = v_P_1580_;
v___y_874_ = v_a_463_;
v___y_875_ = v_a_464_;
goto v___jp_869_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1621_; 
lean_dec(v___x_1578_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_ty_1621_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v_x_817_ = v_x_1405_;
v_ty_818_ = v_ty_1621_;
v_P_819_ = v_P_1580_;
v___y_820_ = v_a_463_;
v___y_821_ = v_a_464_;
goto v___jp_816_;
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1622_; lean_object* v_currMacroScope_1623_; lean_object* v_ref_1624_; lean_object* v_tk_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_xs_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v___x_1578_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_quotContext_1622_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_1622_);
v_currMacroScope_1623_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_1623_);
v_ref_1624_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_1624_);
lean_dec_ref(v_a_463_);
v_tk_1625_ = l_Lean_Syntax_getArg(v_x_1405_, v___x_473_);
lean_dec(v_x_1405_);
v___x_1626_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1627_ = l_Array_extract___redArg(v___x_1626_, v___x_474_, v___x_1303_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1629_ = lean_box(2);
v___x_1630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___x_1628_);
lean_ctor_set(v___x_1630_, 2, v___x_1627_);
v___x_1631_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_474_);
lean_dec(v___x_1468_);
v___x_1632_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1577_);
lean_dec(v___x_475_);
v_xs_1633_ = l_Lean_Syntax_getArgs(v___x_1630_);
lean_dec_ref(v___x_1630_);
v___x_1634_ = l_Lean_SourceInfo_fromRef(v_ref_1624_, v___x_815_);
lean_dec(v_ref_1624_);
v___x_1635_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1636_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1637_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_1623_);
lean_inc(v_quotContext_1622_);
v___x_1638_ = l_Lean_addMacroScope(v_quotContext_1622_, v___x_1637_, v_currMacroScope_1623_);
v___x_1639_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_1634_);
v___x_1640_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1634_);
lean_ctor_set(v___x_1640_, 1, v___x_1636_);
lean_ctor_set(v___x_1640_, 2, v___x_1638_);
lean_ctor_set(v___x_1640_, 3, v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1642_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1643_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_1634_);
v___x_1644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1634_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1646_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_Lean_addMacroScope(v_quotContext_1622_, v___x_1647_, v_currMacroScope_1623_);
v___x_1649_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_1634_);
v___x_1650_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1634_);
lean_ctor_set(v___x_1650_, 1, v___x_1646_);
lean_ctor_set(v___x_1650_, 2, v___x_1648_);
lean_ctor_set(v___x_1650_, 3, v___x_1649_);
lean_inc(v___x_1634_);
v___x_1651_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1645_, v___x_1650_);
lean_inc_ref(v___x_1644_);
lean_inc(v___x_1634_);
v___x_1652_ = l_Lean_Syntax_node2(v___x_1634_, v___x_1642_, v___x_1644_, v___x_1651_);
v___x_1653_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1654_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_1634_);
v___x_1655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1634_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
v___x_1656_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1657_ = l_Lean_SourceInfo_fromRef(v_tk_1625_, v___x_680_);
lean_dec(v_tk_1625_);
v___x_1658_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
lean_inc(v___x_1634_);
v___x_1660_ = l_Lean_Syntax_node1(v___x_1634_, v___x_814_, v___x_1659_);
lean_inc(v___x_1634_);
v___x_1661_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1628_, v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_1663_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
lean_inc(v___x_1634_);
v___x_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1634_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
lean_inc(v___x_1631_);
lean_inc_ref(v___x_1664_);
lean_inc(v___x_1634_);
v___x_1665_ = l_Lean_Syntax_node2(v___x_1634_, v___x_1662_, v___x_1664_, v___x_1631_);
lean_inc(v___x_1634_);
v___x_1666_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1628_, v___x_1665_);
v___x_1667_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_1634_);
v___x_1668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1634_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_1634_);
v___x_1670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1634_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_1634_);
v___x_1672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1634_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1674_ = l_Array_append___redArg(v___x_1673_, v_xs_1633_);
lean_dec_ref(v_xs_1633_);
lean_inc(v___x_1634_);
v___x_1675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1634_);
lean_ctor_set(v___x_1675_, 1, v___x_1628_);
lean_ctor_set(v___x_1675_, 2, v___x_1674_);
lean_inc(v___x_1634_);
v___x_1676_ = l_Lean_Syntax_node2(v___x_1634_, v___x_1628_, v___x_1664_, v___x_1631_);
lean_inc(v___x_1634_);
v___x_1677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1634_);
lean_ctor_set(v___x_1677_, 1, v___x_1628_);
lean_ctor_set(v___x_1677_, 2, v___x_1673_);
v___x_1678_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_1634_);
v___x_1679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1634_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
lean_inc_ref(v___x_1679_);
lean_inc_ref(v___x_1677_);
lean_inc(v___x_1634_);
v___x_1680_ = l_Lean_Syntax_node5(v___x_1634_, v___x_868_, v___x_1644_, v___x_1675_, v___x_1676_, v___x_1677_, v___x_1679_);
lean_inc(v___x_1634_);
v___x_1681_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1628_, v___x_1680_);
v___x_1682_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_1634_);
v___x_1683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1634_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
lean_inc(v___x_1634_);
v___x_1684_ = l_Lean_Syntax_node5(v___x_1634_, v___x_488_, v___x_1672_, v___x_1681_, v___x_1677_, v___x_1683_, v___x_1632_);
lean_inc_ref(v___x_1679_);
lean_inc(v___x_1634_);
v___x_1685_ = l_Lean_Syntax_node3(v___x_1634_, v___x_469_, v___x_1670_, v___x_1684_, v___x_1679_);
lean_inc(v___x_1634_);
v___x_1686_ = l_Lean_Syntax_node4(v___x_1634_, v___x_1656_, v___x_1661_, v___x_1666_, v___x_1668_, v___x_1685_);
lean_inc(v___x_1634_);
v___x_1687_ = l_Lean_Syntax_node2(v___x_1634_, v___x_1654_, v___x_1655_, v___x_1686_);
lean_inc(v___x_1634_);
v___x_1688_ = l_Lean_Syntax_node3(v___x_1634_, v___x_1641_, v___x_1652_, v___x_1687_, v___x_1679_);
lean_inc(v___x_1634_);
v___x_1689_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1628_, v___x_1688_);
v___x_1690_ = l_Lean_Syntax_node2(v___x_1634_, v___x_1635_, v___x_1640_, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v_a_464_);
return v___x_1691_;
}
}
}
}
}
}
v___jp_869_:
{
lean_object* v_quotContext_876_; lean_object* v_currMacroScope_877_; lean_object* v_ref_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_quotContext_876_ = lean_ctor_get(v___y_874_, 1);
lean_inc(v_quotContext_876_);
v_currMacroScope_877_ = lean_ctor_get(v___y_874_, 2);
lean_inc(v_currMacroScope_877_);
v_ref_878_ = lean_ctor_get(v___y_874_, 5);
lean_inc(v_ref_878_);
lean_dec_ref(v___y_874_);
v___x_879_ = l_Lean_SourceInfo_fromRef(v_ref_878_, v___x_815_);
lean_dec(v_ref_878_);
v___x_880_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_881_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_882_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_877_);
lean_inc(v_quotContext_876_);
v___x_883_ = l_Lean_addMacroScope(v_quotContext_876_, v___x_882_, v_currMacroScope_877_);
v___x_884_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_879_);
v___x_885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_885_, 0, v___x_879_);
lean_ctor_set(v___x_885_, 1, v___x_881_);
lean_ctor_set(v___x_885_, 2, v___x_883_);
lean_ctor_set(v___x_885_, 3, v___x_884_);
v___x_886_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_887_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_888_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_889_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_879_);
v___x_890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_879_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_892_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_893_ = lean_box(0);
v___x_894_ = l_Lean_addMacroScope(v_quotContext_876_, v___x_893_, v_currMacroScope_877_);
v___x_895_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_879_);
v___x_896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_896_, 0, v___x_879_);
lean_ctor_set(v___x_896_, 1, v___x_892_);
lean_ctor_set(v___x_896_, 2, v___x_894_);
lean_ctor_set(v___x_896_, 3, v___x_895_);
lean_inc(v___x_879_);
v___x_897_ = l_Lean_Syntax_node1(v___x_879_, v___x_891_, v___x_896_);
lean_inc_ref(v___x_890_);
lean_inc(v___x_879_);
v___x_898_ = l_Lean_Syntax_node2(v___x_879_, v___x_888_, v___x_890_, v___x_897_);
v___x_899_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_900_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_879_);
v___x_901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_879_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
v___x_902_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_879_);
v___x_903_ = l_Lean_Syntax_node1(v___x_879_, v___x_886_, v_x_870_);
v___x_904_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_905_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
lean_inc(v___x_879_);
v___x_906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_879_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
lean_inc(v_ty_872_);
lean_inc_ref(v___x_906_);
lean_inc(v___x_879_);
v___x_907_ = l_Lean_Syntax_node2(v___x_879_, v___x_904_, v___x_906_, v_ty_872_);
lean_inc(v___x_879_);
v___x_908_ = l_Lean_Syntax_node1(v___x_879_, v___x_886_, v___x_907_);
v___x_909_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_879_);
v___x_910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_879_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_879_);
v___x_912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_879_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_879_);
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_879_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_916_ = l_Array_append___redArg(v___x_915_, v_xs_871_);
lean_dec_ref(v_xs_871_);
lean_inc(v___x_879_);
v___x_917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_917_, 0, v___x_879_);
lean_ctor_set(v___x_917_, 1, v___x_886_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
lean_inc(v___x_879_);
v___x_918_ = l_Lean_Syntax_node2(v___x_879_, v___x_886_, v___x_906_, v_ty_872_);
lean_inc(v___x_879_);
v___x_919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_919_, 0, v___x_879_);
lean_ctor_set(v___x_919_, 1, v___x_886_);
lean_ctor_set(v___x_919_, 2, v___x_915_);
v___x_920_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_879_);
v___x_921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_879_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_inc_ref(v___x_921_);
lean_inc_ref(v___x_919_);
lean_inc(v___x_879_);
v___x_922_ = l_Lean_Syntax_node5(v___x_879_, v___x_868_, v___x_890_, v___x_917_, v___x_918_, v___x_919_, v___x_921_);
lean_inc(v___x_879_);
v___x_923_ = l_Lean_Syntax_node1(v___x_879_, v___x_886_, v___x_922_);
v___x_924_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_879_);
v___x_925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_879_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_inc(v___x_879_);
v___x_926_ = l_Lean_Syntax_node5(v___x_879_, v___x_488_, v___x_914_, v___x_923_, v___x_919_, v___x_925_, v_P_873_);
lean_inc_ref(v___x_921_);
lean_inc(v___x_879_);
v___x_927_ = l_Lean_Syntax_node3(v___x_879_, v___x_469_, v___x_912_, v___x_926_, v___x_921_);
lean_inc(v___x_879_);
v___x_928_ = l_Lean_Syntax_node4(v___x_879_, v___x_902_, v___x_903_, v___x_908_, v___x_910_, v___x_927_);
lean_inc(v___x_879_);
v___x_929_ = l_Lean_Syntax_node2(v___x_879_, v___x_900_, v___x_901_, v___x_928_);
lean_inc(v___x_879_);
v___x_930_ = l_Lean_Syntax_node3(v___x_879_, v___x_887_, v___x_898_, v___x_929_, v___x_921_);
lean_inc(v___x_879_);
v___x_931_ = l_Lean_Syntax_node1(v___x_879_, v___x_886_, v___x_930_);
v___x_932_ = l_Lean_Syntax_node2(v___x_879_, v___x_880_, v___x_885_, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___y_875_);
return v___x_933_;
}
v___jp_934_:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = l_Lean_Syntax_getNumArgs(v___x_679_);
v___x_940_ = lean_nat_dec_le(v___x_474_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_813_);
v___x_942_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_941_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; 
lean_inc(v_x_813_);
v___x_943_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_868_);
if (v___x_943_ == 0)
{
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = l_Lean_Syntax_getArg(v_x_813_, v___x_474_);
lean_inc(v___x_944_);
v___x_945_ = l_Lean_Syntax_matchesNull(v___x_944_, v___x_474_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = l_Lean_Syntax_getNumArgs(v___x_944_);
v___x_947_ = lean_nat_dec_le(v___x_474_, v___x_946_);
if (v___x_947_ == 0)
{
lean_dec(v___x_946_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v_x_948_; uint8_t v___x_949_; 
v_x_948_ = l_Lean_Syntax_getArg(v___x_944_, v___x_473_);
lean_inc(v_x_948_);
v___x_949_ = l_Lean_Syntax_isOfKind(v_x_948_, v___x_941_);
if (v___x_949_ == 0)
{
lean_dec(v_x_948_);
lean_dec(v___x_946_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_unsigned_to_nat(2u);
v___x_951_ = l_Lean_Syntax_getArg(v_x_813_, v___x_950_);
lean_inc(v___x_951_);
v___x_952_ = l_Lean_Syntax_matchesNull(v___x_951_, v___x_950_);
if (v___x_952_ == 0)
{
lean_dec(v___x_951_);
lean_dec(v_x_948_);
lean_dec(v___x_946_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_953_ = lean_unsigned_to_nat(3u);
v___x_954_ = l_Lean_Syntax_getArg(v_x_813_, v___x_953_);
lean_dec(v_x_813_);
v___x_955_ = l_Lean_Syntax_matchesNull(v___x_954_, v___x_473_);
if (v___x_955_ == 0)
{
lean_dec(v___x_951_);
lean_dec(v_x_948_);
lean_dec(v___x_946_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_Syntax_matchesNull(v_____discr_935_, v___x_473_);
if (v___x_956_ == 0)
{
lean_dec(v___x_951_);
lean_dec(v_x_948_);
lean_dec(v___x_946_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_ty_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_ys_966_; lean_object* v_xs_967_; 
v___x_957_ = l_Lean_Syntax_getArgs(v___x_944_);
lean_dec(v___x_944_);
v___x_958_ = l_Array_extract___redArg(v___x_957_, v___x_474_, v___x_946_);
lean_dec_ref(v___x_957_);
v_ty_959_ = l_Lean_Syntax_getArg(v___x_951_, v___x_474_);
lean_dec(v___x_951_);
v___x_960_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_961_ = lean_box(2);
v___x_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
lean_ctor_set(v___x_962_, 2, v___x_958_);
v___x_963_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_964_ = l_Array_extract___redArg(v___x_963_, v___x_474_, v___x_939_);
lean_dec_ref(v___x_963_);
v___x_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_965_, 0, v___x_961_);
lean_ctor_set(v___x_965_, 1, v___x_960_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
v_ys_966_ = l_Lean_Syntax_getArgs(v___x_965_);
lean_dec_ref(v___x_965_);
v_xs_967_ = l_Lean_Syntax_getArgs(v___x_962_);
lean_dec_ref(v___x_962_);
v_x_608_ = v_x_948_;
v_xs_609_ = v_xs_967_;
v_ty_610_ = v_ty_959_;
v_ys_611_ = v_ys_966_;
v_P_612_ = v_____discr_936_;
v___y_613_ = v___y_937_;
v___y_614_ = v___y_938_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_x_968_; uint8_t v___x_969_; 
v_x_968_ = l_Lean_Syntax_getArg(v___x_944_, v___x_473_);
lean_inc(v_x_968_);
v___x_969_ = l_Lean_Syntax_isOfKind(v_x_968_, v___x_941_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = l_Lean_Syntax_getNumArgs(v___x_944_);
v___x_971_ = lean_nat_dec_le(v___x_474_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v___x_970_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_969_ == 0)
{
lean_dec(v___x_970_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_unsigned_to_nat(2u);
v___x_973_ = l_Lean_Syntax_getArg(v_x_813_, v___x_972_);
lean_inc(v___x_973_);
v___x_974_ = l_Lean_Syntax_matchesNull(v___x_973_, v___x_972_);
if (v___x_974_ == 0)
{
lean_dec(v___x_973_);
lean_dec(v___x_970_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_unsigned_to_nat(3u);
v___x_976_ = l_Lean_Syntax_getArg(v_x_813_, v___x_975_);
lean_dec(v_x_813_);
v___x_977_ = l_Lean_Syntax_matchesNull(v___x_976_, v___x_473_);
if (v___x_977_ == 0)
{
lean_dec(v___x_973_);
lean_dec(v___x_970_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_Syntax_matchesNull(v_____discr_935_, v___x_473_);
if (v___x_978_ == 0)
{
lean_dec(v___x_973_);
lean_dec(v___x_970_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_ty_987_; lean_object* v_ys_988_; lean_object* v_xs_989_; 
v___x_979_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_980_ = l_Array_extract___redArg(v___x_979_, v___x_474_, v___x_939_);
lean_dec_ref(v___x_979_);
v___x_981_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_982_ = lean_box(2);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_981_);
lean_ctor_set(v___x_983_, 2, v___x_980_);
v___x_984_ = l_Lean_Syntax_getArgs(v___x_944_);
lean_dec(v___x_944_);
v___x_985_ = l_Array_extract___redArg(v___x_984_, v___x_474_, v___x_970_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_986_, 0, v___x_982_);
lean_ctor_set(v___x_986_, 1, v___x_981_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
v_ty_987_ = l_Lean_Syntax_getArg(v___x_973_, v___x_474_);
lean_dec(v___x_973_);
v_ys_988_ = l_Lean_Syntax_getArgs(v___x_983_);
lean_dec_ref(v___x_983_);
v_xs_989_ = l_Lean_Syntax_getArgs(v___x_986_);
lean_dec_ref(v___x_986_);
v_x_608_ = v_x_968_;
v_xs_609_ = v_xs_989_;
v_ty_610_ = v_ty_987_;
v_ys_611_ = v_ys_988_;
v_P_612_ = v_____discr_936_;
v___y_613_ = v___y_937_;
v___y_614_ = v___y_938_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_unsigned_to_nat(2u);
v___x_991_ = l_Lean_Syntax_getArg(v_x_813_, v___x_990_);
lean_inc(v___x_991_);
v___x_992_ = l_Lean_Syntax_matchesNull(v___x_991_, v___x_990_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = l_Lean_Syntax_getNumArgs(v___x_944_);
v___x_994_ = lean_nat_dec_le(v___x_474_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v___x_993_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_969_ == 0)
{
lean_dec(v___x_993_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_992_ == 0)
{
lean_dec(v___x_993_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = lean_unsigned_to_nat(3u);
v___x_996_ = l_Lean_Syntax_getArg(v_x_813_, v___x_995_);
lean_dec(v_x_813_);
v___x_997_ = l_Lean_Syntax_matchesNull(v___x_996_, v___x_473_);
if (v___x_997_ == 0)
{
lean_dec(v___x_993_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_Syntax_matchesNull(v_____discr_935_, v___x_473_);
if (v___x_998_ == 0)
{
lean_dec(v___x_993_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_ty_1007_; lean_object* v_ys_1008_; lean_object* v_xs_1009_; 
v___x_999_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1000_ = l_Array_extract___redArg(v___x_999_, v___x_474_, v___x_939_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1002_ = lean_box(2);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1001_);
lean_ctor_set(v___x_1003_, 2, v___x_1000_);
v___x_1004_ = l_Lean_Syntax_getArgs(v___x_944_);
lean_dec(v___x_944_);
v___x_1005_ = l_Array_extract___redArg(v___x_1004_, v___x_474_, v___x_993_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1002_);
lean_ctor_set(v___x_1006_, 1, v___x_1001_);
lean_ctor_set(v___x_1006_, 2, v___x_1005_);
v_ty_1007_ = l_Lean_Syntax_getArg(v___x_991_, v___x_474_);
lean_dec(v___x_991_);
v_ys_1008_ = l_Lean_Syntax_getArgs(v___x_1003_);
lean_dec_ref(v___x_1003_);
v_xs_1009_ = l_Lean_Syntax_getArgs(v___x_1006_);
lean_dec_ref(v___x_1006_);
v_x_608_ = v_x_968_;
v_xs_609_ = v_xs_1009_;
v_ty_610_ = v_ty_1007_;
v_ys_611_ = v_ys_1008_;
v_P_612_ = v_____discr_936_;
v___y_613_ = v___y_937_;
v___y_614_ = v___y_938_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(3u);
v___x_1011_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1010_);
lean_dec(v_x_813_);
v___x_1012_ = l_Lean_Syntax_matchesNull(v___x_1011_, v___x_473_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = l_Lean_Syntax_getNumArgs(v___x_944_);
v___x_1014_ = lean_nat_dec_le(v___x_474_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_dec(v___x_1013_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_969_ == 0)
{
lean_dec(v___x_1013_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_992_ == 0)
{
lean_dec(v___x_1013_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_1012_ == 0)
{
lean_dec(v___x_1013_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_____discr_935_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Lean_Syntax_matchesNull(v_____discr_935_, v___x_473_);
if (v___x_1015_ == 0)
{
lean_dec(v___x_1013_);
lean_dec(v___x_991_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_ty_1024_; lean_object* v_ys_1025_; lean_object* v_xs_1026_; 
v___x_1016_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1017_ = l_Array_extract___redArg(v___x_1016_, v___x_474_, v___x_939_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1019_ = lean_box(2);
v___x_1020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_1018_);
lean_ctor_set(v___x_1020_, 2, v___x_1017_);
v___x_1021_ = l_Lean_Syntax_getArgs(v___x_944_);
lean_dec(v___x_944_);
v___x_1022_ = l_Array_extract___redArg(v___x_1021_, v___x_474_, v___x_1013_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1019_);
lean_ctor_set(v___x_1023_, 1, v___x_1018_);
lean_ctor_set(v___x_1023_, 2, v___x_1022_);
v_ty_1024_ = l_Lean_Syntax_getArg(v___x_991_, v___x_474_);
lean_dec(v___x_991_);
v_ys_1025_ = l_Lean_Syntax_getArgs(v___x_1020_);
lean_dec_ref(v___x_1020_);
v_xs_1026_ = l_Lean_Syntax_getArgs(v___x_1023_);
lean_dec_ref(v___x_1023_);
v_x_608_ = v_x_968_;
v_xs_609_ = v_xs_1026_;
v_ty_610_ = v_ty_1024_;
v_ys_611_ = v_ys_1025_;
v_P_612_ = v_____discr_936_;
v___y_613_ = v___y_937_;
v___y_614_ = v___y_938_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_ty_1027_ = l_Lean_Syntax_getArg(v___x_991_, v___x_474_);
lean_dec(v___x_991_);
v___x_1028_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1029_ = l_Array_extract___redArg(v___x_1028_, v___x_474_, v___x_939_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1031_ = lean_box(2);
v___x_1032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
lean_ctor_set(v___x_1032_, 2, v___x_1029_);
v___x_1033_ = l_Lean_Syntax_matchesNull(v_____discr_935_, v___x_473_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = l_Lean_Syntax_getNumArgs(v___x_944_);
v___x_1035_ = lean_nat_dec_le(v___x_474_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1032_);
lean_dec(v_ty_1027_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_969_ == 0)
{
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1032_);
lean_dec(v_ty_1027_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_992_ == 0)
{
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1032_);
lean_dec(v_ty_1027_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_1012_ == 0)
{
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1032_);
lean_dec(v_ty_1027_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
if (v___x_1033_ == 0)
{
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1032_);
lean_dec(v_ty_1027_);
lean_dec(v_x_968_);
lean_dec(v___x_944_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v_ys_1039_; lean_object* v_xs_1040_; 
v___x_1036_ = l_Lean_Syntax_getArgs(v___x_944_);
lean_dec(v___x_944_);
v___x_1037_ = l_Array_extract___redArg(v___x_1036_, v___x_474_, v___x_1034_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1031_);
lean_ctor_set(v___x_1038_, 1, v___x_1030_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
v_ys_1039_ = l_Lean_Syntax_getArgs(v___x_1032_);
lean_dec_ref(v___x_1032_);
v_xs_1040_ = l_Lean_Syntax_getArgs(v___x_1038_);
lean_dec_ref(v___x_1038_);
v_x_608_ = v_x_968_;
v_xs_609_ = v_xs_1040_;
v_ty_610_ = v_ty_1027_;
v_ys_611_ = v_ys_1039_;
v_P_612_ = v_____discr_936_;
v___y_613_ = v___y_937_;
v___y_614_ = v___y_938_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1041_; 
lean_dec(v___x_944_);
v_xs_1041_ = l_Lean_Syntax_getArgs(v___x_1032_);
lean_dec_ref(v___x_1032_);
v_x_546_ = v_x_968_;
v_ty_547_ = v_ty_1027_;
v_xs_548_ = v_xs_1041_;
v_P_549_ = v_____discr_936_;
v___y_550_ = v___y_937_;
v___y_551_ = v___y_938_;
goto v___jp_545_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Lean_Syntax_matchesNull(v_____discr_935_, v___x_473_);
if (v___x_1042_ == 0)
{
lean_dec(v___x_939_);
lean_dec_ref(v___y_937_);
lean_dec(v_____discr_936_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v___y_466_ = v___y_938_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_xs_1048_; 
v___x_1043_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1044_ = l_Array_extract___redArg(v___x_1043_, v___x_474_, v___x_939_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1046_ = lean_box(2);
v___x_1047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1045_);
lean_ctor_set(v___x_1047_, 2, v___x_1044_);
v_xs_1048_ = l_Lean_Syntax_getArgs(v___x_1047_);
lean_dec_ref(v___x_1047_);
v_x_490_ = v_x_813_;
v_xs_491_ = v_xs_1048_;
v_P_492_ = v_____discr_936_;
v___y_493_ = v___y_937_;
v___y_494_ = v___y_938_;
goto v___jp_489_;
}
}
}
}
}
else
{
lean_object* v_tk_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_tk_1692_ = l_Lean_Syntax_getArg(v_x_813_, v___x_473_);
v___x_1693_ = lean_unsigned_to_nat(2u);
v___x_1694_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1693_);
lean_inc(v___x_1694_);
v___x_1695_ = l_Lean_Syntax_matchesNull(v___x_1694_, v___x_473_);
if (v___x_1695_ == 0)
{
uint8_t v___x_1696_; 
lean_inc(v___x_1694_);
v___x_1696_ = l_Lean_Syntax_matchesNull(v___x_1694_, v___x_474_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; uint8_t v___x_1698_; 
lean_dec(v___x_1694_);
lean_dec(v_tk_1692_);
v___x_1697_ = l_Lean_Syntax_getNumArgs(v___x_679_);
v___x_1698_ = lean_nat_dec_le(v___x_474_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1699_; lean_object* v_P_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1699_ = lean_unsigned_to_nat(4u);
v_P_1700_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1699_);
lean_dec(v___x_475_);
v___x_1701_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_813_);
v___x_1702_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_813_);
v___x_1704_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1705_ = lean_unsigned_to_nat(3u);
v___x_1706_ = l_Lean_Syntax_getArg(v_x_813_, v___x_474_);
lean_inc(v___x_1706_);
v___x_1707_ = l_Lean_Syntax_matchesNull(v___x_1706_, v___x_474_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = l_Lean_Syntax_getNumArgs(v___x_1706_);
v___x_1709_ = lean_nat_dec_le(v___x_474_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec(v___x_1708_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v_x_1710_; uint8_t v___x_1711_; 
v_x_1710_ = l_Lean_Syntax_getArg(v___x_1706_, v___x_473_);
lean_inc(v_x_1710_);
v___x_1711_ = l_Lean_Syntax_isOfKind(v_x_1710_, v___x_1701_);
if (v___x_1711_ == 0)
{
lean_dec(v_x_1710_);
lean_dec(v___x_1708_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1693_);
lean_inc(v___x_1712_);
v___x_1713_ = l_Lean_Syntax_matchesNull(v___x_1712_, v___x_1693_);
if (v___x_1713_ == 0)
{
lean_dec(v___x_1712_);
lean_dec(v_x_1710_);
lean_dec(v___x_1708_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1705_);
lean_dec(v_x_813_);
v___x_1715_ = l_Lean_Syntax_matchesNull(v___x_1714_, v___x_473_);
if (v___x_1715_ == 0)
{
lean_dec(v___x_1712_);
lean_dec(v_x_1710_);
lean_dec(v___x_1708_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1712_);
lean_dec(v_x_1710_);
lean_dec(v___x_1708_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_ty_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v_ys_1725_; lean_object* v_xs_1726_; 
v___x_1716_ = l_Lean_Syntax_getArgs(v___x_1706_);
lean_dec(v___x_1706_);
v___x_1717_ = l_Array_extract___redArg(v___x_1716_, v___x_474_, v___x_1708_);
lean_dec_ref(v___x_1716_);
v_ty_1718_ = l_Lean_Syntax_getArg(v___x_1712_, v___x_474_);
lean_dec(v___x_1712_);
v___x_1719_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1720_ = lean_box(2);
v___x_1721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set(v___x_1721_, 1, v___x_1719_);
lean_ctor_set(v___x_1721_, 2, v___x_1717_);
v___x_1722_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1723_ = l_Array_extract___redArg(v___x_1722_, v___x_474_, v___x_1697_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1720_);
lean_ctor_set(v___x_1724_, 1, v___x_1719_);
lean_ctor_set(v___x_1724_, 2, v___x_1723_);
v_ys_1725_ = l_Lean_Syntax_getArgs(v___x_1724_);
lean_dec_ref(v___x_1724_);
v_xs_1726_ = l_Lean_Syntax_getArgs(v___x_1721_);
lean_dec_ref(v___x_1721_);
v_x_608_ = v_x_1710_;
v_xs_609_ = v_xs_1726_;
v_ty_610_ = v_ty_1718_;
v_ys_611_ = v_ys_1725_;
v_P_612_ = v_P_1700_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_x_1727_; uint8_t v___x_1728_; 
v_x_1727_ = l_Lean_Syntax_getArg(v___x_1706_, v___x_473_);
lean_inc(v_x_1727_);
v___x_1728_ = l_Lean_Syntax_isOfKind(v_x_1727_, v___x_1701_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = l_Lean_Syntax_getNumArgs(v___x_1706_);
v___x_1730_ = lean_nat_dec_le(v___x_474_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_dec(v___x_1729_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1728_ == 0)
{
lean_dec(v___x_1729_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1693_);
lean_inc(v___x_1731_);
v___x_1732_ = l_Lean_Syntax_matchesNull(v___x_1731_, v___x_1693_);
if (v___x_1732_ == 0)
{
lean_dec(v___x_1731_);
lean_dec(v___x_1729_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1705_);
lean_dec(v_x_813_);
v___x_1734_ = l_Lean_Syntax_matchesNull(v___x_1733_, v___x_473_);
if (v___x_1734_ == 0)
{
lean_dec(v___x_1731_);
lean_dec(v___x_1729_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1731_);
lean_dec(v___x_1729_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v_ty_1743_; lean_object* v_ys_1744_; lean_object* v_xs_1745_; 
v___x_1735_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1736_ = l_Array_extract___redArg(v___x_1735_, v___x_474_, v___x_1697_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1738_ = lean_box(2);
v___x_1739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___x_1737_);
lean_ctor_set(v___x_1739_, 2, v___x_1736_);
v___x_1740_ = l_Lean_Syntax_getArgs(v___x_1706_);
lean_dec(v___x_1706_);
v___x_1741_ = l_Array_extract___redArg(v___x_1740_, v___x_474_, v___x_1729_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1738_);
lean_ctor_set(v___x_1742_, 1, v___x_1737_);
lean_ctor_set(v___x_1742_, 2, v___x_1741_);
v_ty_1743_ = l_Lean_Syntax_getArg(v___x_1731_, v___x_474_);
lean_dec(v___x_1731_);
v_ys_1744_ = l_Lean_Syntax_getArgs(v___x_1739_);
lean_dec_ref(v___x_1739_);
v_xs_1745_ = l_Lean_Syntax_getArgs(v___x_1742_);
lean_dec_ref(v___x_1742_);
v_x_608_ = v_x_1727_;
v_xs_609_ = v_xs_1745_;
v_ty_610_ = v_ty_1743_;
v_ys_611_ = v_ys_1744_;
v_P_612_ = v_P_1700_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1693_);
lean_inc(v___x_1746_);
v___x_1747_ = l_Lean_Syntax_matchesNull(v___x_1746_, v___x_1693_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = l_Lean_Syntax_getNumArgs(v___x_1706_);
v___x_1749_ = lean_nat_dec_le(v___x_474_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_dec(v___x_1748_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1728_ == 0)
{
lean_dec(v___x_1748_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1747_ == 0)
{
lean_dec(v___x_1748_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1705_);
lean_dec(v_x_813_);
v___x_1751_ = l_Lean_Syntax_matchesNull(v___x_1750_, v___x_473_);
if (v___x_1751_ == 0)
{
lean_dec(v___x_1748_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1748_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_ty_1760_; lean_object* v_ys_1761_; lean_object* v_xs_1762_; 
v___x_1752_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1753_ = l_Array_extract___redArg(v___x_1752_, v___x_474_, v___x_1697_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1755_ = lean_box(2);
v___x_1756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1754_);
lean_ctor_set(v___x_1756_, 2, v___x_1753_);
v___x_1757_ = l_Lean_Syntax_getArgs(v___x_1706_);
lean_dec(v___x_1706_);
v___x_1758_ = l_Array_extract___redArg(v___x_1757_, v___x_474_, v___x_1748_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1755_);
lean_ctor_set(v___x_1759_, 1, v___x_1754_);
lean_ctor_set(v___x_1759_, 2, v___x_1758_);
v_ty_1760_ = l_Lean_Syntax_getArg(v___x_1746_, v___x_474_);
lean_dec(v___x_1746_);
v_ys_1761_ = l_Lean_Syntax_getArgs(v___x_1756_);
lean_dec_ref(v___x_1756_);
v_xs_1762_ = l_Lean_Syntax_getArgs(v___x_1759_);
lean_dec_ref(v___x_1759_);
v_x_608_ = v_x_1727_;
v_xs_609_ = v_xs_1762_;
v_ty_610_ = v_ty_1760_;
v_ys_611_ = v_ys_1761_;
v_P_612_ = v_P_1700_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1705_);
lean_dec(v_x_813_);
v___x_1764_ = l_Lean_Syntax_matchesNull(v___x_1763_, v___x_473_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = l_Lean_Syntax_getNumArgs(v___x_1706_);
v___x_1766_ = lean_nat_dec_le(v___x_474_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_dec(v___x_1765_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1728_ == 0)
{
lean_dec(v___x_1765_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1747_ == 0)
{
lean_dec(v___x_1765_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1764_ == 0)
{
lean_dec(v___x_1765_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1765_);
lean_dec(v___x_1746_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_ty_1775_; lean_object* v_ys_1776_; lean_object* v_xs_1777_; 
v___x_1767_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1768_ = l_Array_extract___redArg(v___x_1767_, v___x_474_, v___x_1697_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1770_ = lean_box(2);
v___x_1771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
lean_ctor_set(v___x_1771_, 2, v___x_1768_);
v___x_1772_ = l_Lean_Syntax_getArgs(v___x_1706_);
lean_dec(v___x_1706_);
v___x_1773_ = l_Array_extract___redArg(v___x_1772_, v___x_474_, v___x_1765_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1770_);
lean_ctor_set(v___x_1774_, 1, v___x_1769_);
lean_ctor_set(v___x_1774_, 2, v___x_1773_);
v_ty_1775_ = l_Lean_Syntax_getArg(v___x_1746_, v___x_474_);
lean_dec(v___x_1746_);
v_ys_1776_ = l_Lean_Syntax_getArgs(v___x_1771_);
lean_dec_ref(v___x_1771_);
v_xs_1777_ = l_Lean_Syntax_getArgs(v___x_1774_);
lean_dec_ref(v___x_1774_);
v_x_608_ = v_x_1727_;
v_xs_609_ = v_xs_1777_;
v_ty_610_ = v_ty_1775_;
v_ys_611_ = v_ys_1776_;
v_P_612_ = v_P_1700_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_ty_1778_ = l_Lean_Syntax_getArg(v___x_1746_, v___x_474_);
lean_dec(v___x_1746_);
v___x_1779_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1780_ = l_Array_extract___redArg(v___x_1779_, v___x_474_, v___x_1697_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1782_ = lean_box(2);
v___x_1783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v___x_1781_);
lean_ctor_set(v___x_1783_, 2, v___x_1780_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = l_Lean_Syntax_getNumArgs(v___x_1706_);
v___x_1785_ = lean_nat_dec_le(v___x_474_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec(v___x_1784_);
lean_dec_ref(v___x_1783_);
lean_dec(v_ty_1778_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1728_ == 0)
{
lean_dec(v___x_1784_);
lean_dec_ref(v___x_1783_);
lean_dec(v_ty_1778_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1747_ == 0)
{
lean_dec(v___x_1784_);
lean_dec_ref(v___x_1783_);
lean_dec(v_ty_1778_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1764_ == 0)
{
lean_dec(v___x_1784_);
lean_dec_ref(v___x_1783_);
lean_dec(v_ty_1778_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1784_);
lean_dec_ref(v___x_1783_);
lean_dec(v_ty_1778_);
lean_dec(v_x_1727_);
lean_dec(v___x_1706_);
lean_dec(v_P_1700_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_ys_1789_; lean_object* v_xs_1790_; 
v___x_1786_ = l_Lean_Syntax_getArgs(v___x_1706_);
lean_dec(v___x_1706_);
v___x_1787_ = l_Array_extract___redArg(v___x_1786_, v___x_474_, v___x_1784_);
lean_dec_ref(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1782_);
lean_ctor_set(v___x_1788_, 1, v___x_1781_);
lean_ctor_set(v___x_1788_, 2, v___x_1787_);
v_ys_1789_ = l_Lean_Syntax_getArgs(v___x_1783_);
lean_dec_ref(v___x_1783_);
v_xs_1790_ = l_Lean_Syntax_getArgs(v___x_1788_);
lean_dec_ref(v___x_1788_);
v_x_608_ = v_x_1727_;
v_xs_609_ = v_xs_1790_;
v_ty_610_ = v_ty_1778_;
v_ys_611_ = v_ys_1789_;
v_P_612_ = v_P_1700_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1791_; 
lean_dec(v___x_1706_);
v_xs_1791_ = l_Lean_Syntax_getArgs(v___x_1783_);
lean_dec_ref(v___x_1783_);
v_x_546_ = v_x_1727_;
v_ty_547_ = v_ty_1778_;
v_xs_548_ = v_xs_1791_;
v_P_549_ = v_P_1700_;
v___y_550_ = v_a_463_;
v___y_551_ = v_a_464_;
goto v___jp_545_;
}
}
}
}
}
}
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v_P_1700_);
lean_dec(v___x_1697_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_xs_1797_; 
v___x_1792_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1793_ = l_Array_extract___redArg(v___x_1792_, v___x_474_, v___x_1697_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1795_ = lean_box(2);
v___x_1796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___x_1794_);
lean_ctor_set(v___x_1796_, 2, v___x_1793_);
v_xs_1797_ = l_Lean_Syntax_getArgs(v___x_1796_);
lean_dec_ref(v___x_1796_);
v_x_490_ = v_x_813_;
v_xs_491_ = v_xs_1797_;
v_P_492_ = v_P_1700_;
v___y_493_ = v_a_463_;
v___y_494_ = v_a_464_;
goto v___jp_489_;
}
}
}
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = l_Lean_Syntax_getArg(v___x_1694_, v___x_473_);
lean_dec(v___x_1694_);
v___x_1799_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
lean_inc(v___x_1798_);
v___x_1800_ = l_Lean_Syntax_isOfKind(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_dec(v___x_1798_);
lean_dec(v_tk_1692_);
v___x_1801_ = l_Lean_Syntax_getNumArgs(v___x_679_);
v___x_1802_ = lean_nat_dec_le(v___x_474_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1803_; lean_object* v_P_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1803_ = lean_unsigned_to_nat(4u);
v_P_1804_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1803_);
lean_dec(v___x_475_);
v___x_1805_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_813_);
v___x_1806_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_813_);
v___x_1808_ = l_Lean_Syntax_isOfKind(v_x_813_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = lean_unsigned_to_nat(3u);
v___x_1810_ = l_Lean_Syntax_getArg(v_x_813_, v___x_474_);
lean_inc(v___x_1810_);
v___x_1811_ = l_Lean_Syntax_matchesNull(v___x_1810_, v___x_474_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = l_Lean_Syntax_getNumArgs(v___x_1810_);
v___x_1813_ = lean_nat_dec_le(v___x_474_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_dec(v___x_1812_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v_x_1814_; uint8_t v___x_1815_; 
v_x_1814_ = l_Lean_Syntax_getArg(v___x_1810_, v___x_473_);
lean_inc(v_x_1814_);
v___x_1815_ = l_Lean_Syntax_isOfKind(v_x_1814_, v___x_1805_);
if (v___x_1815_ == 0)
{
lean_dec(v_x_1814_);
lean_dec(v___x_1812_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1693_);
lean_inc(v___x_1816_);
v___x_1817_ = l_Lean_Syntax_matchesNull(v___x_1816_, v___x_1693_);
if (v___x_1817_ == 0)
{
lean_dec(v___x_1816_);
lean_dec(v_x_1814_);
lean_dec(v___x_1812_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1809_);
lean_dec(v_x_813_);
v___x_1819_ = l_Lean_Syntax_matchesNull(v___x_1818_, v___x_473_);
if (v___x_1819_ == 0)
{
lean_dec(v___x_1816_);
lean_dec(v_x_1814_);
lean_dec(v___x_1812_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1816_);
lean_dec(v_x_1814_);
lean_dec(v___x_1812_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_ty_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_ys_1829_; lean_object* v_xs_1830_; 
v___x_1820_ = l_Lean_Syntax_getArgs(v___x_1810_);
lean_dec(v___x_1810_);
v___x_1821_ = l_Array_extract___redArg(v___x_1820_, v___x_474_, v___x_1812_);
lean_dec_ref(v___x_1820_);
v_ty_1822_ = l_Lean_Syntax_getArg(v___x_1816_, v___x_474_);
lean_dec(v___x_1816_);
v___x_1823_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1824_ = lean_box(2);
v___x_1825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1823_);
lean_ctor_set(v___x_1825_, 2, v___x_1821_);
v___x_1826_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1827_ = l_Array_extract___redArg(v___x_1826_, v___x_474_, v___x_1801_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1824_);
lean_ctor_set(v___x_1828_, 1, v___x_1823_);
lean_ctor_set(v___x_1828_, 2, v___x_1827_);
v_ys_1829_ = l_Lean_Syntax_getArgs(v___x_1828_);
lean_dec_ref(v___x_1828_);
v_xs_1830_ = l_Lean_Syntax_getArgs(v___x_1825_);
lean_dec_ref(v___x_1825_);
v_x_608_ = v_x_1814_;
v_xs_609_ = v_xs_1830_;
v_ty_610_ = v_ty_1822_;
v_ys_611_ = v_ys_1829_;
v_P_612_ = v_P_1804_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_x_1831_; uint8_t v___x_1832_; 
v_x_1831_ = l_Lean_Syntax_getArg(v___x_1810_, v___x_473_);
lean_inc(v_x_1831_);
v___x_1832_ = l_Lean_Syntax_isOfKind(v_x_1831_, v___x_1805_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = l_Lean_Syntax_getNumArgs(v___x_1810_);
v___x_1834_ = lean_nat_dec_le(v___x_474_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec(v___x_1833_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1832_ == 0)
{
lean_dec(v___x_1833_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1693_);
lean_inc(v___x_1835_);
v___x_1836_ = l_Lean_Syntax_matchesNull(v___x_1835_, v___x_1693_);
if (v___x_1836_ == 0)
{
lean_dec(v___x_1835_);
lean_dec(v___x_1833_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1809_);
lean_dec(v_x_813_);
v___x_1838_ = l_Lean_Syntax_matchesNull(v___x_1837_, v___x_473_);
if (v___x_1838_ == 0)
{
lean_dec(v___x_1835_);
lean_dec(v___x_1833_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1835_);
lean_dec(v___x_1833_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_ty_1847_; lean_object* v_ys_1848_; lean_object* v_xs_1849_; 
v___x_1839_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1840_ = l_Array_extract___redArg(v___x_1839_, v___x_474_, v___x_1801_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1842_ = lean_box(2);
v___x_1843_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1841_);
lean_ctor_set(v___x_1843_, 2, v___x_1840_);
v___x_1844_ = l_Lean_Syntax_getArgs(v___x_1810_);
lean_dec(v___x_1810_);
v___x_1845_ = l_Array_extract___redArg(v___x_1844_, v___x_474_, v___x_1833_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1842_);
lean_ctor_set(v___x_1846_, 1, v___x_1841_);
lean_ctor_set(v___x_1846_, 2, v___x_1845_);
v_ty_1847_ = l_Lean_Syntax_getArg(v___x_1835_, v___x_474_);
lean_dec(v___x_1835_);
v_ys_1848_ = l_Lean_Syntax_getArgs(v___x_1843_);
lean_dec_ref(v___x_1843_);
v_xs_1849_ = l_Lean_Syntax_getArgs(v___x_1846_);
lean_dec_ref(v___x_1846_);
v_x_608_ = v_x_1831_;
v_xs_609_ = v_xs_1849_;
v_ty_610_ = v_ty_1847_;
v_ys_611_ = v_ys_1848_;
v_P_612_ = v_P_1804_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1693_);
lean_inc(v___x_1850_);
v___x_1851_ = l_Lean_Syntax_matchesNull(v___x_1850_, v___x_1693_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = l_Lean_Syntax_getNumArgs(v___x_1810_);
v___x_1853_ = lean_nat_dec_le(v___x_474_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec(v___x_1852_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1832_ == 0)
{
lean_dec(v___x_1852_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1851_ == 0)
{
lean_dec(v___x_1852_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1809_);
lean_dec(v_x_813_);
v___x_1855_ = l_Lean_Syntax_matchesNull(v___x_1854_, v___x_473_);
if (v___x_1855_ == 0)
{
lean_dec(v___x_1852_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1852_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_ty_1864_; lean_object* v_ys_1865_; lean_object* v_xs_1866_; 
v___x_1856_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1857_ = l_Array_extract___redArg(v___x_1856_, v___x_474_, v___x_1801_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1859_ = lean_box(2);
v___x_1860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___x_1858_);
lean_ctor_set(v___x_1860_, 2, v___x_1857_);
v___x_1861_ = l_Lean_Syntax_getArgs(v___x_1810_);
lean_dec(v___x_1810_);
v___x_1862_ = l_Array_extract___redArg(v___x_1861_, v___x_474_, v___x_1852_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1859_);
lean_ctor_set(v___x_1863_, 1, v___x_1858_);
lean_ctor_set(v___x_1863_, 2, v___x_1862_);
v_ty_1864_ = l_Lean_Syntax_getArg(v___x_1850_, v___x_474_);
lean_dec(v___x_1850_);
v_ys_1865_ = l_Lean_Syntax_getArgs(v___x_1860_);
lean_dec_ref(v___x_1860_);
v_xs_1866_ = l_Lean_Syntax_getArgs(v___x_1863_);
lean_dec_ref(v___x_1863_);
v_x_608_ = v_x_1831_;
v_xs_609_ = v_xs_1866_;
v_ty_610_ = v_ty_1864_;
v_ys_611_ = v_ys_1865_;
v_P_612_ = v_P_1804_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = l_Lean_Syntax_getArg(v_x_813_, v___x_1809_);
lean_dec(v_x_813_);
v___x_1868_ = l_Lean_Syntax_matchesNull(v___x_1867_, v___x_473_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = l_Lean_Syntax_getNumArgs(v___x_1810_);
v___x_1870_ = lean_nat_dec_le(v___x_474_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_dec(v___x_1869_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1832_ == 0)
{
lean_dec(v___x_1869_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1851_ == 0)
{
lean_dec(v___x_1869_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1868_ == 0)
{
lean_dec(v___x_1869_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1869_);
lean_dec(v___x_1850_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_ty_1879_; lean_object* v_ys_1880_; lean_object* v_xs_1881_; 
v___x_1871_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1872_ = l_Array_extract___redArg(v___x_1871_, v___x_474_, v___x_1801_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1874_ = lean_box(2);
v___x_1875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1873_);
lean_ctor_set(v___x_1875_, 2, v___x_1872_);
v___x_1876_ = l_Lean_Syntax_getArgs(v___x_1810_);
lean_dec(v___x_1810_);
v___x_1877_ = l_Array_extract___redArg(v___x_1876_, v___x_474_, v___x_1869_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1874_);
lean_ctor_set(v___x_1878_, 1, v___x_1873_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
v_ty_1879_ = l_Lean_Syntax_getArg(v___x_1850_, v___x_474_);
lean_dec(v___x_1850_);
v_ys_1880_ = l_Lean_Syntax_getArgs(v___x_1875_);
lean_dec_ref(v___x_1875_);
v_xs_1881_ = l_Lean_Syntax_getArgs(v___x_1878_);
lean_dec_ref(v___x_1878_);
v_x_608_ = v_x_1831_;
v_xs_609_ = v_xs_1881_;
v_ty_610_ = v_ty_1879_;
v_ys_611_ = v_ys_1880_;
v_P_612_ = v_P_1804_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_ty_1882_ = l_Lean_Syntax_getArg(v___x_1850_, v___x_474_);
lean_dec(v___x_1850_);
v___x_1883_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1884_ = l_Array_extract___redArg(v___x_1883_, v___x_474_, v___x_1801_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1886_ = lean_box(2);
v___x_1887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set(v___x_1887_, 1, v___x_1885_);
lean_ctor_set(v___x_1887_, 2, v___x_1884_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = l_Lean_Syntax_getNumArgs(v___x_1810_);
v___x_1889_ = lean_nat_dec_le(v___x_474_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1887_);
lean_dec(v_ty_1882_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1832_ == 0)
{
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1887_);
lean_dec(v_ty_1882_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1851_ == 0)
{
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1887_);
lean_dec(v_ty_1882_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1868_ == 0)
{
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1887_);
lean_dec(v_ty_1882_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1887_);
lean_dec(v_ty_1882_);
lean_dec(v_x_1831_);
lean_dec(v___x_1810_);
lean_dec(v_P_1804_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_ys_1893_; lean_object* v_xs_1894_; 
v___x_1890_ = l_Lean_Syntax_getArgs(v___x_1810_);
lean_dec(v___x_1810_);
v___x_1891_ = l_Array_extract___redArg(v___x_1890_, v___x_474_, v___x_1888_);
lean_dec_ref(v___x_1890_);
v___x_1892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1886_);
lean_ctor_set(v___x_1892_, 1, v___x_1885_);
lean_ctor_set(v___x_1892_, 2, v___x_1891_);
v_ys_1893_ = l_Lean_Syntax_getArgs(v___x_1887_);
lean_dec_ref(v___x_1887_);
v_xs_1894_ = l_Lean_Syntax_getArgs(v___x_1892_);
lean_dec_ref(v___x_1892_);
v_x_608_ = v_x_1831_;
v_xs_609_ = v_xs_1894_;
v_ty_610_ = v_ty_1882_;
v_ys_611_ = v_ys_1893_;
v_P_612_ = v_P_1804_;
v___y_613_ = v_a_463_;
v___y_614_ = v_a_464_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1895_; 
lean_dec(v___x_1810_);
v_xs_1895_ = l_Lean_Syntax_getArgs(v___x_1887_);
lean_dec_ref(v___x_1887_);
v_x_546_ = v_x_1831_;
v_ty_547_ = v_ty_1882_;
v_xs_548_ = v_xs_1895_;
v_P_549_ = v_P_1804_;
v___y_550_ = v_a_463_;
v___y_551_ = v_a_464_;
goto v___jp_545_;
}
}
}
}
}
}
}
else
{
if (v___x_1695_ == 0)
{
lean_dec(v_P_1804_);
lean_dec(v___x_1801_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
lean_dec_ref(v_a_463_);
v___y_466_ = v_a_464_;
goto v___jp_465_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_xs_1901_; 
v___x_1896_ = l_Lean_Syntax_getArgs(v___x_679_);
lean_dec(v___x_679_);
v___x_1897_ = l_Array_extract___redArg(v___x_1896_, v___x_474_, v___x_1801_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1899_ = lean_box(2);
v___x_1900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1898_);
lean_ctor_set(v___x_1900_, 2, v___x_1897_);
v_xs_1901_ = l_Lean_Syntax_getArgs(v___x_1900_);
lean_dec_ref(v___x_1900_);
v_x_490_ = v_x_813_;
v_xs_491_ = v_xs_1901_;
v_P_492_ = v_P_1804_;
v___y_493_ = v_a_463_;
v___y_494_ = v_a_464_;
goto v___jp_489_;
}
}
}
}
else
{
lean_object* v_quotContext_1902_; lean_object* v_currMacroScope_1903_; lean_object* v_ref_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_quotContext_1902_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_1902_);
v_currMacroScope_1903_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_1903_);
v_ref_1904_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_1904_);
lean_dec_ref(v_a_463_);
v___x_1905_ = l_Lean_Syntax_getArg(v___x_1798_, v___x_474_);
lean_dec(v___x_1798_);
v___x_1906_ = lean_unsigned_to_nat(4u);
v___x_1907_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1906_);
lean_dec(v___x_475_);
v___x_1908_ = l_Lean_SourceInfo_fromRef(v_ref_1904_, v___x_1695_);
lean_dec(v_ref_1904_);
v___x_1909_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1910_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1911_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_1903_);
lean_inc(v_quotContext_1902_);
v___x_1912_ = l_Lean_addMacroScope(v_quotContext_1902_, v___x_1911_, v_currMacroScope_1903_);
v___x_1913_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_1908_);
v___x_1914_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1908_);
lean_ctor_set(v___x_1914_, 1, v___x_1910_);
lean_ctor_set(v___x_1914_, 2, v___x_1912_);
lean_ctor_set(v___x_1914_, 3, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1916_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1917_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1918_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_1908_);
v___x_1919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1908_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1921_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1922_ = lean_box(0);
v___x_1923_ = l_Lean_addMacroScope(v_quotContext_1902_, v___x_1922_, v_currMacroScope_1903_);
v___x_1924_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_1908_);
v___x_1925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1908_);
lean_ctor_set(v___x_1925_, 1, v___x_1921_);
lean_ctor_set(v___x_1925_, 2, v___x_1923_);
lean_ctor_set(v___x_1925_, 3, v___x_1924_);
lean_inc(v___x_1908_);
v___x_1926_ = l_Lean_Syntax_node1(v___x_1908_, v___x_1920_, v___x_1925_);
lean_inc(v___x_1908_);
v___x_1927_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1917_, v___x_1919_, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1929_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_1908_);
v___x_1930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1908_);
lean_ctor_set(v___x_1930_, 1, v___x_1928_);
v___x_1931_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1932_ = l_Lean_SourceInfo_fromRef(v_tk_1692_, v___x_680_);
lean_dec(v_tk_1692_);
v___x_1933_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
lean_inc(v___x_1908_);
v___x_1935_ = l_Lean_Syntax_node1(v___x_1908_, v___x_814_, v___x_1934_);
lean_inc(v___x_1908_);
v___x_1936_ = l_Lean_Syntax_node1(v___x_1908_, v___x_1915_, v___x_1935_);
v___x_1937_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
lean_inc(v___x_1908_);
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1908_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
lean_inc(v___x_1908_);
v___x_1939_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1799_, v___x_1938_, v___x_1905_);
lean_inc(v___x_1908_);
v___x_1940_ = l_Lean_Syntax_node1(v___x_1908_, v___x_1915_, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_1908_);
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1908_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_1908_);
v___x_1944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1908_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_1908_);
v___x_1946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1908_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
lean_inc_ref(v___x_1946_);
lean_inc(v___x_1908_);
v___x_1947_ = l_Lean_Syntax_node3(v___x_1908_, v___x_469_, v___x_1944_, v___x_1907_, v___x_1946_);
lean_inc(v___x_1908_);
v___x_1948_ = l_Lean_Syntax_node4(v___x_1908_, v___x_1931_, v___x_1936_, v___x_1940_, v___x_1942_, v___x_1947_);
lean_inc(v___x_1908_);
v___x_1949_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1929_, v___x_1930_, v___x_1948_);
lean_inc(v___x_1908_);
v___x_1950_ = l_Lean_Syntax_node3(v___x_1908_, v___x_1916_, v___x_1927_, v___x_1949_, v___x_1946_);
lean_inc(v___x_1908_);
v___x_1951_ = l_Lean_Syntax_node1(v___x_1908_, v___x_1915_, v___x_1950_);
v___x_1952_ = l_Lean_Syntax_node2(v___x_1908_, v___x_1909_, v___x_1914_, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
lean_ctor_set(v___x_1953_, 1, v_a_464_);
return v___x_1953_;
}
}
}
else
{
lean_object* v_quotContext_1954_; lean_object* v_currMacroScope_1955_; lean_object* v_ref_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec(v___x_1694_);
lean_dec(v_x_813_);
lean_dec(v___x_679_);
v_quotContext_1954_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_1954_);
v_currMacroScope_1955_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_1955_);
v_ref_1956_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_1956_);
lean_dec_ref(v_a_463_);
v___x_1957_ = lean_unsigned_to_nat(4u);
v___x_1958_ = l_Lean_Syntax_getArg(v___x_475_, v___x_1957_);
lean_dec(v___x_475_);
v___x_1959_ = l_Lean_SourceInfo_fromRef(v_ref_1956_, v___x_487_);
lean_dec(v_ref_1956_);
v___x_1960_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1961_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1962_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_1955_);
lean_inc(v_quotContext_1954_);
v___x_1963_ = l_Lean_addMacroScope(v_quotContext_1954_, v___x_1962_, v_currMacroScope_1955_);
v___x_1964_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_1959_);
v___x_1965_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1959_);
lean_ctor_set(v___x_1965_, 1, v___x_1961_);
lean_ctor_set(v___x_1965_, 2, v___x_1963_);
lean_ctor_set(v___x_1965_, 3, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1967_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1968_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1969_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_1959_);
v___x_1970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1959_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1972_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1973_ = lean_box(0);
v___x_1974_ = l_Lean_addMacroScope(v_quotContext_1954_, v___x_1973_, v_currMacroScope_1955_);
v___x_1975_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_1959_);
v___x_1976_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1959_);
lean_ctor_set(v___x_1976_, 1, v___x_1972_);
lean_ctor_set(v___x_1976_, 2, v___x_1974_);
lean_ctor_set(v___x_1976_, 3, v___x_1975_);
lean_inc(v___x_1959_);
v___x_1977_ = l_Lean_Syntax_node1(v___x_1959_, v___x_1971_, v___x_1976_);
lean_inc(v___x_1959_);
v___x_1978_ = l_Lean_Syntax_node2(v___x_1959_, v___x_1968_, v___x_1970_, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1980_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_1959_);
v___x_1981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1959_);
lean_ctor_set(v___x_1981_, 1, v___x_1979_);
v___x_1982_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1983_ = l_Lean_SourceInfo_fromRef(v_tk_1692_, v___x_680_);
lean_dec(v_tk_1692_);
v___x_1984_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
lean_inc(v___x_1959_);
v___x_1986_ = l_Lean_Syntax_node1(v___x_1959_, v___x_814_, v___x_1985_);
lean_inc(v___x_1959_);
v___x_1987_ = l_Lean_Syntax_node1(v___x_1959_, v___x_1966_, v___x_1986_);
v___x_1988_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_1959_);
v___x_1989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1959_);
lean_ctor_set(v___x_1989_, 1, v___x_1966_);
lean_ctor_set(v___x_1989_, 2, v___x_1988_);
v___x_1990_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_1959_);
v___x_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1959_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_1959_);
v___x_1993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1959_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_1959_);
v___x_1995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1959_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
lean_inc_ref(v___x_1995_);
lean_inc(v___x_1959_);
v___x_1996_ = l_Lean_Syntax_node3(v___x_1959_, v___x_469_, v___x_1993_, v___x_1958_, v___x_1995_);
lean_inc(v___x_1959_);
v___x_1997_ = l_Lean_Syntax_node4(v___x_1959_, v___x_1982_, v___x_1987_, v___x_1989_, v___x_1991_, v___x_1996_);
lean_inc(v___x_1959_);
v___x_1998_ = l_Lean_Syntax_node2(v___x_1959_, v___x_1980_, v___x_1981_, v___x_1997_);
lean_inc(v___x_1959_);
v___x_1999_ = l_Lean_Syntax_node3(v___x_1959_, v___x_1967_, v___x_1978_, v___x_1998_, v___x_1995_);
lean_inc(v___x_1959_);
v___x_2000_ = l_Lean_Syntax_node1(v___x_1959_, v___x_1966_, v___x_1999_);
v___x_2001_ = l_Lean_Syntax_node2(v___x_1959_, v___x_1960_, v___x_1965_, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v_a_464_);
return v___x_2002_;
}
}
v___jp_816_:
{
lean_object* v_quotContext_822_; lean_object* v_currMacroScope_823_; lean_object* v_ref_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_quotContext_822_ = lean_ctor_get(v___y_820_, 1);
lean_inc(v_quotContext_822_);
v_currMacroScope_823_ = lean_ctor_get(v___y_820_, 2);
lean_inc(v_currMacroScope_823_);
v_ref_824_ = lean_ctor_get(v___y_820_, 5);
lean_inc(v_ref_824_);
lean_dec_ref(v___y_820_);
v___x_825_ = l_Lean_SourceInfo_fromRef(v_ref_824_, v___x_815_);
lean_dec(v_ref_824_);
v___x_826_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_827_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_828_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_823_);
lean_inc(v_quotContext_822_);
v___x_829_ = l_Lean_addMacroScope(v_quotContext_822_, v___x_828_, v_currMacroScope_823_);
v___x_830_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_825_);
v___x_831_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_831_, 0, v___x_825_);
lean_ctor_set(v___x_831_, 1, v___x_827_);
lean_ctor_set(v___x_831_, 2, v___x_829_);
lean_ctor_set(v___x_831_, 3, v___x_830_);
v___x_832_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_833_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_834_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_835_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_825_);
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_825_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_838_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_839_ = lean_box(0);
v___x_840_ = l_Lean_addMacroScope(v_quotContext_822_, v___x_839_, v_currMacroScope_823_);
v___x_841_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_825_);
v___x_842_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_842_, 0, v___x_825_);
lean_ctor_set(v___x_842_, 1, v___x_838_);
lean_ctor_set(v___x_842_, 2, v___x_840_);
lean_ctor_set(v___x_842_, 3, v___x_841_);
lean_inc(v___x_825_);
v___x_843_ = l_Lean_Syntax_node1(v___x_825_, v___x_837_, v___x_842_);
lean_inc(v___x_825_);
v___x_844_ = l_Lean_Syntax_node2(v___x_825_, v___x_834_, v___x_836_, v___x_843_);
v___x_845_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_846_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_825_);
v___x_847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_825_);
lean_ctor_set(v___x_847_, 1, v___x_845_);
v___x_848_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_825_);
v___x_849_ = l_Lean_Syntax_node1(v___x_825_, v___x_832_, v_x_817_);
v___x_850_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_851_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
lean_inc(v___x_825_);
v___x_852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_825_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
lean_inc(v___x_825_);
v___x_853_ = l_Lean_Syntax_node2(v___x_825_, v___x_850_, v___x_852_, v_ty_818_);
lean_inc(v___x_825_);
v___x_854_ = l_Lean_Syntax_node1(v___x_825_, v___x_832_, v___x_853_);
v___x_855_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_825_);
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_825_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_825_);
v___x_858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_825_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_825_);
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_825_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
lean_inc_ref(v___x_860_);
lean_inc(v___x_825_);
v___x_861_ = l_Lean_Syntax_node3(v___x_825_, v___x_469_, v___x_858_, v_P_819_, v___x_860_);
lean_inc(v___x_825_);
v___x_862_ = l_Lean_Syntax_node4(v___x_825_, v___x_848_, v___x_849_, v___x_854_, v___x_856_, v___x_861_);
lean_inc(v___x_825_);
v___x_863_ = l_Lean_Syntax_node2(v___x_825_, v___x_846_, v___x_847_, v___x_862_);
lean_inc(v___x_825_);
v___x_864_ = l_Lean_Syntax_node3(v___x_825_, v___x_833_, v___x_844_, v___x_863_, v___x_860_);
lean_inc(v___x_825_);
v___x_865_ = l_Lean_Syntax_node1(v___x_825_, v___x_832_, v___x_864_);
v___x_866_ = l_Lean_Syntax_node2(v___x_825_, v___x_826_, v___x_831_, v___x_865_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___y_821_);
return v___x_867_;
}
}
}
v___jp_489_:
{
lean_object* v_quotContext_495_; lean_object* v_currMacroScope_496_; lean_object* v_ref_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_quotContext_495_ = lean_ctor_get(v___y_493_, 1);
lean_inc(v_quotContext_495_);
v_currMacroScope_496_ = lean_ctor_get(v___y_493_, 2);
lean_inc(v_currMacroScope_496_);
v_ref_497_ = lean_ctor_get(v___y_493_, 5);
lean_inc(v_ref_497_);
lean_dec_ref(v___y_493_);
v___x_498_ = l_Lean_SourceInfo_fromRef(v_ref_497_, v___x_487_);
lean_dec(v_ref_497_);
v___x_499_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_500_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_501_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_496_);
lean_inc(v_quotContext_495_);
v___x_502_ = l_Lean_addMacroScope(v_quotContext_495_, v___x_501_, v_currMacroScope_496_);
v___x_503_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_498_);
v___x_504_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_504_, 0, v___x_498_);
lean_ctor_set(v___x_504_, 1, v___x_500_);
lean_ctor_set(v___x_504_, 2, v___x_502_);
lean_ctor_set(v___x_504_, 3, v___x_503_);
v___x_505_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_506_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_507_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_508_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_498_);
v___x_509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_498_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_511_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_512_ = lean_box(0);
v___x_513_ = l_Lean_addMacroScope(v_quotContext_495_, v___x_512_, v_currMacroScope_496_);
v___x_514_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_498_);
v___x_515_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_515_, 0, v___x_498_);
lean_ctor_set(v___x_515_, 1, v___x_511_);
lean_ctor_set(v___x_515_, 2, v___x_513_);
lean_ctor_set(v___x_515_, 3, v___x_514_);
lean_inc(v___x_498_);
v___x_516_ = l_Lean_Syntax_node1(v___x_498_, v___x_510_, v___x_515_);
lean_inc(v___x_498_);
v___x_517_ = l_Lean_Syntax_node2(v___x_498_, v___x_507_, v___x_509_, v___x_516_);
v___x_518_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_519_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_498_);
v___x_520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_498_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
v___x_521_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_498_);
v___x_522_ = l_Lean_Syntax_node1(v___x_498_, v___x_505_, v_x_490_);
v___x_523_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_498_);
v___x_524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_524_, 0, v___x_498_);
lean_ctor_set(v___x_524_, 1, v___x_505_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
v___x_525_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_498_);
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_498_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_498_);
v___x_528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_498_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_498_);
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_498_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Array_append___redArg(v___x_523_, v_xs_491_);
lean_dec_ref(v_xs_491_);
lean_inc(v___x_498_);
v___x_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_532_, 0, v___x_498_);
lean_ctor_set(v___x_532_, 1, v___x_505_);
lean_ctor_set(v___x_532_, 2, v___x_531_);
v___x_533_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_498_);
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_498_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_inc_ref(v___x_524_);
lean_inc(v___x_498_);
v___x_535_ = l_Lean_Syntax_node5(v___x_498_, v___x_488_, v___x_530_, v___x_532_, v___x_524_, v___x_534_, v_P_492_);
v___x_536_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_498_);
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_498_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_inc_ref(v___x_537_);
lean_inc(v___x_498_);
v___x_538_ = l_Lean_Syntax_node3(v___x_498_, v___x_469_, v___x_528_, v___x_535_, v___x_537_);
lean_inc(v___x_498_);
v___x_539_ = l_Lean_Syntax_node4(v___x_498_, v___x_521_, v___x_522_, v___x_524_, v___x_526_, v___x_538_);
lean_inc(v___x_498_);
v___x_540_ = l_Lean_Syntax_node2(v___x_498_, v___x_519_, v___x_520_, v___x_539_);
lean_inc(v___x_498_);
v___x_541_ = l_Lean_Syntax_node3(v___x_498_, v___x_506_, v___x_517_, v___x_540_, v___x_537_);
lean_inc(v___x_498_);
v___x_542_ = l_Lean_Syntax_node1(v___x_498_, v___x_505_, v___x_541_);
v___x_543_ = l_Lean_Syntax_node2(v___x_498_, v___x_499_, v___x_504_, v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___y_494_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v_quotContext_552_; lean_object* v_currMacroScope_553_; lean_object* v_ref_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_quotContext_552_ = lean_ctor_get(v___y_550_, 1);
lean_inc(v_quotContext_552_);
v_currMacroScope_553_ = lean_ctor_get(v___y_550_, 2);
lean_inc(v_currMacroScope_553_);
v_ref_554_ = lean_ctor_get(v___y_550_, 5);
lean_inc(v_ref_554_);
lean_dec_ref(v___y_550_);
v___x_555_ = l_Lean_SourceInfo_fromRef(v_ref_554_, v___x_487_);
lean_dec(v_ref_554_);
v___x_556_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_557_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_558_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_553_);
lean_inc(v_quotContext_552_);
v___x_559_ = l_Lean_addMacroScope(v_quotContext_552_, v___x_558_, v_currMacroScope_553_);
v___x_560_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_555_);
v___x_561_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_561_, 0, v___x_555_);
lean_ctor_set(v___x_561_, 1, v___x_557_);
lean_ctor_set(v___x_561_, 2, v___x_559_);
lean_ctor_set(v___x_561_, 3, v___x_560_);
v___x_562_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_563_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_564_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_565_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_555_);
v___x_566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_555_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_568_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_569_ = lean_box(0);
v___x_570_ = l_Lean_addMacroScope(v_quotContext_552_, v___x_569_, v_currMacroScope_553_);
v___x_571_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_555_);
v___x_572_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_572_, 0, v___x_555_);
lean_ctor_set(v___x_572_, 1, v___x_568_);
lean_ctor_set(v___x_572_, 2, v___x_570_);
lean_ctor_set(v___x_572_, 3, v___x_571_);
lean_inc(v___x_555_);
v___x_573_ = l_Lean_Syntax_node1(v___x_555_, v___x_567_, v___x_572_);
lean_inc(v___x_555_);
v___x_574_ = l_Lean_Syntax_node2(v___x_555_, v___x_564_, v___x_566_, v___x_573_);
v___x_575_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_576_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_555_);
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_555_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
v___x_578_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_555_);
v___x_579_ = l_Lean_Syntax_node1(v___x_555_, v___x_562_, v_x_546_);
v___x_580_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_581_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
lean_inc(v___x_555_);
v___x_582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_555_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
lean_inc(v___x_555_);
v___x_583_ = l_Lean_Syntax_node2(v___x_555_, v___x_580_, v___x_582_, v_ty_547_);
lean_inc(v___x_555_);
v___x_584_ = l_Lean_Syntax_node1(v___x_555_, v___x_562_, v___x_583_);
v___x_585_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_555_);
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_555_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_555_);
v___x_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_555_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_555_);
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_555_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_592_ = l_Array_append___redArg(v___x_591_, v_xs_548_);
lean_dec_ref(v_xs_548_);
lean_inc(v___x_555_);
v___x_593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_555_);
lean_ctor_set(v___x_593_, 1, v___x_562_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
lean_inc(v___x_555_);
v___x_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_555_);
lean_ctor_set(v___x_594_, 1, v___x_562_);
lean_ctor_set(v___x_594_, 2, v___x_591_);
v___x_595_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_555_);
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_555_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_inc(v___x_555_);
v___x_597_ = l_Lean_Syntax_node5(v___x_555_, v___x_488_, v___x_590_, v___x_593_, v___x_594_, v___x_596_, v_P_549_);
v___x_598_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_555_);
v___x_599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_555_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_inc_ref(v___x_599_);
lean_inc(v___x_555_);
v___x_600_ = l_Lean_Syntax_node3(v___x_555_, v___x_469_, v___x_588_, v___x_597_, v___x_599_);
lean_inc(v___x_555_);
v___x_601_ = l_Lean_Syntax_node4(v___x_555_, v___x_578_, v___x_579_, v___x_584_, v___x_586_, v___x_600_);
lean_inc(v___x_555_);
v___x_602_ = l_Lean_Syntax_node2(v___x_555_, v___x_576_, v___x_577_, v___x_601_);
lean_inc(v___x_555_);
v___x_603_ = l_Lean_Syntax_node3(v___x_555_, v___x_563_, v___x_574_, v___x_602_, v___x_599_);
lean_inc(v___x_555_);
v___x_604_ = l_Lean_Syntax_node1(v___x_555_, v___x_562_, v___x_603_);
v___x_605_ = l_Lean_Syntax_node2(v___x_555_, v___x_556_, v___x_561_, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___y_551_);
return v___x_606_;
}
v___jp_607_:
{
lean_object* v_quotContext_615_; lean_object* v_currMacroScope_616_; lean_object* v_ref_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_quotContext_615_ = lean_ctor_get(v___y_613_, 1);
lean_inc(v_quotContext_615_);
v_currMacroScope_616_ = lean_ctor_get(v___y_613_, 2);
lean_inc(v_currMacroScope_616_);
v_ref_617_ = lean_ctor_get(v___y_613_, 5);
lean_inc(v_ref_617_);
lean_dec_ref(v___y_613_);
v___x_618_ = l_Lean_SourceInfo_fromRef(v_ref_617_, v___x_487_);
lean_dec(v_ref_617_);
v___x_619_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_620_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_621_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc(v_currMacroScope_616_);
lean_inc(v_quotContext_615_);
v___x_622_ = l_Lean_addMacroScope(v_quotContext_615_, v___x_621_, v_currMacroScope_616_);
v___x_623_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc(v___x_618_);
v___x_624_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_624_, 0, v___x_618_);
lean_ctor_set(v___x_624_, 1, v___x_620_);
lean_ctor_set(v___x_624_, 2, v___x_622_);
lean_ctor_set(v___x_624_, 3, v___x_623_);
v___x_625_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_626_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_627_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_628_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_618_);
v___x_629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_618_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_631_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_632_ = lean_box(0);
v___x_633_ = l_Lean_addMacroScope(v_quotContext_615_, v___x_632_, v_currMacroScope_616_);
v___x_634_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
lean_inc(v___x_618_);
v___x_635_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_635_, 0, v___x_618_);
lean_ctor_set(v___x_635_, 1, v___x_631_);
lean_ctor_set(v___x_635_, 2, v___x_633_);
lean_ctor_set(v___x_635_, 3, v___x_634_);
lean_inc(v___x_618_);
v___x_636_ = l_Lean_Syntax_node1(v___x_618_, v___x_630_, v___x_635_);
lean_inc_ref(v___x_629_);
lean_inc(v___x_618_);
v___x_637_ = l_Lean_Syntax_node2(v___x_618_, v___x_627_, v___x_629_, v___x_636_);
v___x_638_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_639_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_618_);
v___x_640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_618_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
v___x_641_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_618_);
v___x_642_ = l_Lean_Syntax_node1(v___x_618_, v___x_625_, v_x_608_);
v___x_643_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_644_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
lean_inc(v___x_618_);
v___x_645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_618_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_inc(v_ty_610_);
lean_inc_ref(v___x_645_);
lean_inc(v___x_618_);
v___x_646_ = l_Lean_Syntax_node2(v___x_618_, v___x_643_, v___x_645_, v_ty_610_);
lean_inc(v___x_618_);
v___x_647_ = l_Lean_Syntax_node1(v___x_618_, v___x_625_, v___x_646_);
v___x_648_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_618_);
v___x_649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_618_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_618_);
v___x_651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_618_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_618_);
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_618_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
v___x_655_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_656_ = l_Array_append___redArg(v___x_655_, v_xs_609_);
lean_dec_ref(v_xs_609_);
lean_inc(v___x_618_);
v___x_657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_618_);
lean_ctor_set(v___x_657_, 1, v___x_625_);
lean_ctor_set(v___x_657_, 2, v___x_656_);
lean_inc(v___x_618_);
v___x_658_ = l_Lean_Syntax_node2(v___x_618_, v___x_625_, v___x_645_, v_ty_610_);
lean_inc(v___x_618_);
v___x_659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_659_, 0, v___x_618_);
lean_ctor_set(v___x_659_, 1, v___x_625_);
lean_ctor_set(v___x_659_, 2, v___x_655_);
v___x_660_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_618_);
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_618_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_inc_ref(v___x_661_);
lean_inc_ref(v___x_659_);
lean_inc(v___x_618_);
v___x_662_ = l_Lean_Syntax_node5(v___x_618_, v___x_654_, v___x_629_, v___x_657_, v___x_658_, v___x_659_, v___x_661_);
v___x_663_ = l_Array_mkArray1___redArg(v___x_662_);
v___x_664_ = l_Array_append___redArg(v___x_663_, v_ys_611_);
lean_dec_ref(v_ys_611_);
lean_inc(v___x_618_);
v___x_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_618_);
lean_ctor_set(v___x_665_, 1, v___x_625_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
v___x_666_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_618_);
v___x_667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_618_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc(v___x_618_);
v___x_668_ = l_Lean_Syntax_node5(v___x_618_, v___x_488_, v___x_653_, v___x_665_, v___x_659_, v___x_667_, v_P_612_);
lean_inc_ref(v___x_661_);
lean_inc(v___x_618_);
v___x_669_ = l_Lean_Syntax_node3(v___x_618_, v___x_469_, v___x_651_, v___x_668_, v___x_661_);
lean_inc(v___x_618_);
v___x_670_ = l_Lean_Syntax_node4(v___x_618_, v___x_641_, v___x_642_, v___x_647_, v___x_649_, v___x_669_);
lean_inc(v___x_618_);
v___x_671_ = l_Lean_Syntax_node2(v___x_618_, v___x_639_, v___x_640_, v___x_670_);
lean_inc(v___x_618_);
v___x_672_ = l_Lean_Syntax_node3(v___x_618_, v___x_626_, v___x_637_, v___x_671_, v___x_661_);
lean_inc(v___x_618_);
v___x_673_ = l_Lean_Syntax_node1(v___x_618_, v___x_625_, v___x_672_);
v___x_674_ = l_Lean_Syntax_node2(v___x_618_, v___x_619_, v___x_624_, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___y_614_);
return v___x_675_;
}
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = l_Lean_Syntax_getArg(v___x_475_, v___x_474_);
v___x_2004_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
lean_inc(v___x_2003_);
v___x_2005_ = l_Lean_Syntax_isOfKind(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec(v___x_2003_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_463_);
v___x_2006_ = lean_box(1);
v___x_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v_a_464_);
return v___x_2007_;
}
else
{
lean_object* v_ref_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_ref_2008_ = lean_ctor_get(v_a_463_, 5);
v___x_2009_ = lean_unsigned_to_nat(3u);
v___x_2010_ = l_Lean_Syntax_getArg(v___x_475_, v___x_2009_);
lean_dec(v___x_475_);
v___x_2011_ = l_Lean_SourceInfo_fromRef(v_ref_2008_, v___x_485_);
v___x_2012_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2011_);
v___x_2013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2011_);
v___x_2015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2011_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = l_Lean_Syntax_node3(v___x_2011_, v___x_469_, v___x_2013_, v___x_2010_, v___x_2015_);
v___x_2017_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67));
v___x_2018_ = l_Lean_expandExplicitBinders(v___x_2017_, v___x_2003_, v___x_2016_, v_a_463_, v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v___x_2003_);
return v___x_2018_;
}
}
}
else
{
lean_object* v_quotContext_2019_; lean_object* v_currMacroScope_2020_; lean_object* v_ref_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_quotContext_2019_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_2019_);
v_currMacroScope_2020_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_2020_);
v_ref_2021_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_2021_);
lean_dec_ref(v_a_463_);
v___x_2022_ = l_Lean_Syntax_getArg(v___x_475_, v___x_473_);
v___x_2023_ = lean_unsigned_to_nat(2u);
v___x_2024_ = l_Lean_Syntax_getArg(v___x_475_, v___x_2023_);
lean_dec(v___x_475_);
v___x_2025_ = l_Lean_SourceInfo_fromRef(v_ref_2021_, v___x_483_);
lean_dec(v_ref_2021_);
v___x_2026_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2027_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69);
v___x_2028_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71));
v___x_2029_ = l_Lean_addMacroScope(v_quotContext_2019_, v___x_2028_, v_currMacroScope_2020_);
v___x_2030_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__74));
lean_inc(v___x_2025_);
v___x_2031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2025_);
lean_ctor_set(v___x_2031_, 1, v___x_2027_);
lean_ctor_set(v___x_2031_, 2, v___x_2029_);
lean_ctor_set(v___x_2031_, 3, v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2033_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2025_);
v___x_2034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2025_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2025_);
v___x_2036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2025_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
lean_inc_ref(v___x_2036_);
lean_inc_ref(v___x_2034_);
lean_inc(v___x_2025_);
v___x_2037_ = l_Lean_Syntax_node3(v___x_2025_, v___x_469_, v___x_2034_, v___x_2022_, v___x_2036_);
lean_inc(v___x_2025_);
v___x_2038_ = l_Lean_Syntax_node3(v___x_2025_, v___x_469_, v___x_2034_, v___x_2024_, v___x_2036_);
lean_inc(v___x_2025_);
v___x_2039_ = l_Lean_Syntax_node2(v___x_2025_, v___x_2032_, v___x_2037_, v___x_2038_);
v___x_2040_ = l_Lean_Syntax_node2(v___x_2025_, v___x_2026_, v___x_2031_, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v_a_464_);
return v___x_2041_;
}
}
else
{
lean_object* v_quotContext_2042_; lean_object* v_currMacroScope_2043_; lean_object* v_ref_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_quotContext_2042_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_2042_);
v_currMacroScope_2043_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_2043_);
v_ref_2044_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_2044_);
lean_dec_ref(v_a_463_);
v___x_2045_ = l_Lean_Syntax_getArg(v___x_475_, v___x_473_);
v___x_2046_ = lean_unsigned_to_nat(2u);
v___x_2047_ = l_Lean_Syntax_getArg(v___x_475_, v___x_2046_);
lean_dec(v___x_475_);
v___x_2048_ = l_Lean_SourceInfo_fromRef(v_ref_2044_, v___x_481_);
lean_dec(v_ref_2044_);
v___x_2049_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2050_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76);
v___x_2051_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78));
v___x_2052_ = l_Lean_addMacroScope(v_quotContext_2042_, v___x_2051_, v_currMacroScope_2043_);
v___x_2053_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__81));
lean_inc(v___x_2048_);
v___x_2054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2048_);
lean_ctor_set(v___x_2054_, 1, v___x_2050_);
lean_ctor_set(v___x_2054_, 2, v___x_2052_);
lean_ctor_set(v___x_2054_, 3, v___x_2053_);
v___x_2055_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2056_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2048_);
v___x_2057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2048_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2048_);
v___x_2059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2048_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
lean_inc_ref(v___x_2059_);
lean_inc_ref(v___x_2057_);
lean_inc(v___x_2048_);
v___x_2060_ = l_Lean_Syntax_node3(v___x_2048_, v___x_469_, v___x_2057_, v___x_2045_, v___x_2059_);
lean_inc(v___x_2048_);
v___x_2061_ = l_Lean_Syntax_node3(v___x_2048_, v___x_469_, v___x_2057_, v___x_2047_, v___x_2059_);
lean_inc(v___x_2048_);
v___x_2062_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2055_, v___x_2060_, v___x_2061_);
v___x_2063_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2049_, v___x_2054_, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_a_464_);
return v___x_2064_;
}
}
else
{
lean_object* v_quotContext_2065_; lean_object* v_currMacroScope_2066_; lean_object* v_ref_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_quotContext_2065_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_2065_);
v_currMacroScope_2066_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_2066_);
v_ref_2067_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_2067_);
lean_dec_ref(v_a_463_);
v___x_2068_ = l_Lean_Syntax_getArg(v___x_475_, v___x_474_);
lean_dec(v___x_475_);
v___x_2069_ = l_Lean_SourceInfo_fromRef(v_ref_2067_, v___x_479_);
lean_dec(v_ref_2067_);
v___x_2070_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2071_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83);
v___x_2072_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85));
v___x_2073_ = l_Lean_addMacroScope(v_quotContext_2065_, v___x_2072_, v_currMacroScope_2066_);
v___x_2074_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__90));
lean_inc(v___x_2069_);
v___x_2075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2069_);
lean_ctor_set(v___x_2075_, 1, v___x_2071_);
lean_ctor_set(v___x_2075_, 2, v___x_2073_);
lean_ctor_set(v___x_2075_, 3, v___x_2074_);
v___x_2076_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2077_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2069_);
v___x_2078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2069_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2069_);
v___x_2080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2069_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
lean_inc(v___x_2069_);
v___x_2081_ = l_Lean_Syntax_node3(v___x_2069_, v___x_469_, v___x_2078_, v___x_2068_, v___x_2080_);
lean_inc(v___x_2069_);
v___x_2082_ = l_Lean_Syntax_node1(v___x_2069_, v___x_2076_, v___x_2081_);
v___x_2083_ = l_Lean_Syntax_node2(v___x_2069_, v___x_2070_, v___x_2075_, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v_a_464_);
return v___x_2084_;
}
}
else
{
lean_object* v_quotContext_2085_; lean_object* v_currMacroScope_2086_; lean_object* v_ref_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_quotContext_2085_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_2085_);
v_currMacroScope_2086_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_2086_);
v_ref_2087_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_2087_);
lean_dec_ref(v_a_463_);
v___x_2088_ = l_Lean_Syntax_getArg(v___x_475_, v___x_473_);
v___x_2089_ = lean_unsigned_to_nat(2u);
v___x_2090_ = l_Lean_Syntax_getArg(v___x_475_, v___x_2089_);
lean_dec(v___x_475_);
v___x_2091_ = l_Lean_SourceInfo_fromRef(v_ref_2087_, v___x_477_);
lean_dec(v_ref_2087_);
v___x_2092_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2093_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92);
v___x_2094_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94));
v___x_2095_ = l_Lean_addMacroScope(v_quotContext_2085_, v___x_2094_, v_currMacroScope_2086_);
v___x_2096_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__97));
lean_inc(v___x_2091_);
v___x_2097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2091_);
lean_ctor_set(v___x_2097_, 1, v___x_2093_);
lean_ctor_set(v___x_2097_, 2, v___x_2095_);
lean_ctor_set(v___x_2097_, 3, v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2099_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2091_);
v___x_2100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2091_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2091_);
v___x_2102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2091_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
lean_inc_ref(v___x_2102_);
lean_inc_ref(v___x_2100_);
lean_inc(v___x_2091_);
v___x_2103_ = l_Lean_Syntax_node3(v___x_2091_, v___x_469_, v___x_2100_, v___x_2088_, v___x_2102_);
lean_inc(v___x_2091_);
v___x_2104_ = l_Lean_Syntax_node3(v___x_2091_, v___x_469_, v___x_2100_, v___x_2090_, v___x_2102_);
lean_inc(v___x_2091_);
v___x_2105_ = l_Lean_Syntax_node2(v___x_2091_, v___x_2098_, v___x_2103_, v___x_2104_);
v___x_2106_ = l_Lean_Syntax_node2(v___x_2091_, v___x_2092_, v___x_2097_, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v_a_464_);
return v___x_2107_;
}
}
else
{
lean_object* v_quotContext_2108_; lean_object* v_currMacroScope_2109_; lean_object* v_ref_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_quotContext_2108_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_quotContext_2108_);
v_currMacroScope_2109_ = lean_ctor_get(v_a_463_, 2);
lean_inc(v_currMacroScope_2109_);
v_ref_2110_ = lean_ctor_get(v_a_463_, 5);
lean_inc(v_ref_2110_);
lean_dec_ref(v_a_463_);
v___x_2111_ = l_Lean_Syntax_getArg(v___x_475_, v___x_473_);
v___x_2112_ = lean_unsigned_to_nat(2u);
v___x_2113_ = l_Lean_Syntax_getArg(v___x_475_, v___x_2112_);
lean_dec(v___x_475_);
v___x_2114_ = 0;
v___x_2115_ = l_Lean_SourceInfo_fromRef(v_ref_2110_, v___x_2114_);
lean_dec(v_ref_2110_);
v___x_2116_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2117_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99);
v___x_2118_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101));
v___x_2119_ = l_Lean_addMacroScope(v_quotContext_2108_, v___x_2118_, v_currMacroScope_2109_);
v___x_2120_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__104));
lean_inc(v___x_2115_);
v___x_2121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2115_);
lean_ctor_set(v___x_2121_, 1, v___x_2117_);
lean_ctor_set(v___x_2121_, 2, v___x_2119_);
lean_ctor_set(v___x_2121_, 3, v___x_2120_);
v___x_2122_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2123_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2115_);
v___x_2124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2115_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2115_);
v___x_2126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2115_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
lean_inc_ref(v___x_2126_);
lean_inc_ref(v___x_2124_);
lean_inc(v___x_2115_);
v___x_2127_ = l_Lean_Syntax_node3(v___x_2115_, v___x_469_, v___x_2124_, v___x_2111_, v___x_2126_);
lean_inc(v___x_2115_);
v___x_2128_ = l_Lean_Syntax_node3(v___x_2115_, v___x_469_, v___x_2124_, v___x_2113_, v___x_2126_);
lean_inc(v___x_2115_);
v___x_2129_ = l_Lean_Syntax_node2(v___x_2115_, v___x_2122_, v___x_2127_, v___x_2128_);
v___x_2130_ = l_Lean_Syntax_node2(v___x_2115_, v___x_2116_, v___x_2121_, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v_a_464_);
return v___x_2131_;
}
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_box(1);
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___y_466_);
return v___x_468_;
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0));
v___x_2134_ = l_String_toRawSubstring_x27(v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(lean_object* v_x_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
lean_inc(v_x_2148_);
v___x_2152_ = l_Lean_Syntax_isOfKind(v_x_2148_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v_a_2149_);
lean_dec(v_x_2148_);
v___x_2153_ = lean_box(1);
v___x_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v_a_2150_);
return v___x_2154_;
}
else
{
lean_object* v_quotContext_2155_; lean_object* v_currMacroScope_2156_; lean_object* v_ref_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_quotContext_2155_ = lean_ctor_get(v_a_2149_, 1);
lean_inc(v_quotContext_2155_);
v_currMacroScope_2156_ = lean_ctor_get(v_a_2149_, 2);
lean_inc(v_currMacroScope_2156_);
v_ref_2157_ = lean_ctor_get(v_a_2149_, 5);
lean_inc(v_ref_2157_);
lean_dec_ref(v_a_2149_);
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2158_);
lean_dec(v_x_2148_);
v___x_2160_ = 0;
v___x_2161_ = l_Lean_SourceInfo_fromRef(v_ref_2157_, v___x_2160_);
lean_dec(v_ref_2157_);
v___x_2162_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2163_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1);
v___x_2164_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3));
lean_inc(v_currMacroScope_2156_);
lean_inc(v_quotContext_2155_);
v___x_2165_ = l_Lean_addMacroScope(v_quotContext_2155_, v___x_2164_, v_currMacroScope_2156_);
v___x_2166_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8));
lean_inc(v___x_2161_);
v___x_2167_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2161_);
lean_ctor_set(v___x_2167_, 1, v___x_2163_);
lean_ctor_set(v___x_2167_, 2, v___x_2165_);
lean_ctor_set(v___x_2167_, 3, v___x_2166_);
v___x_2168_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2169_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2170_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc(v___x_2161_);
v___x_2171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2161_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1);
v___x_2173_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_2174_ = l_Lean_addMacroScope(v_quotContext_2155_, v___x_2173_, v_currMacroScope_2156_);
v___x_2175_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__6));
lean_inc(v___x_2161_);
v___x_2176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2161_);
lean_ctor_set(v___x_2176_, 1, v___x_2172_);
lean_ctor_set(v___x_2176_, 2, v___x_2174_);
lean_ctor_set(v___x_2176_, 3, v___x_2175_);
v___x_2177_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
lean_inc(v___x_2161_);
v___x_2178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2161_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
lean_inc(v___x_2161_);
v___x_2179_ = l_Lean_Syntax_node3(v___x_2161_, v___x_2169_, v___x_2171_, v___x_2176_, v___x_2178_);
v___x_2180_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2181_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2161_);
v___x_2182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2161_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2161_);
v___x_2184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2161_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
lean_inc(v___x_2161_);
v___x_2185_ = l_Lean_Syntax_node3(v___x_2161_, v___x_2180_, v___x_2182_, v___x_2159_, v___x_2184_);
lean_inc(v___x_2161_);
v___x_2186_ = l_Lean_Syntax_node2(v___x_2161_, v___x_2168_, v___x_2179_, v___x_2185_);
v___x_2187_ = l_Lean_Syntax_node2(v___x_2161_, v___x_2162_, v___x_2167_, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v_a_2150_);
return v___x_2188_;
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__0));
v___x_2191_ = l_String_toRawSubstring_x27(v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(lean_object* v_x_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
lean_inc(v_x_2207_);
v___x_2211_ = l_Lean_Syntax_isOfKind(v_x_2207_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v_a_2208_);
lean_dec(v_x_2207_);
v___x_2212_ = lean_box(1);
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v_a_2209_);
return v___x_2213_;
}
else
{
lean_object* v_quotContext_2214_; lean_object* v_currMacroScope_2215_; lean_object* v_ref_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_quotContext_2214_ = lean_ctor_get(v_a_2208_, 1);
lean_inc(v_quotContext_2214_);
v_currMacroScope_2215_ = lean_ctor_get(v_a_2208_, 2);
lean_inc(v_currMacroScope_2215_);
v_ref_2216_ = lean_ctor_get(v_a_2208_, 5);
lean_inc(v_ref_2216_);
lean_dec_ref(v_a_2208_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = l_Lean_Syntax_getArg(v_x_2207_, v___x_2217_);
v___x_2219_ = lean_unsigned_to_nat(2u);
v___x_2220_ = l_Lean_Syntax_getArg(v_x_2207_, v___x_2219_);
lean_dec(v_x_2207_);
v___x_2221_ = 0;
v___x_2222_ = l_Lean_SourceInfo_fromRef(v_ref_2216_, v___x_2221_);
lean_dec(v_ref_2216_);
v___x_2223_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2224_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1);
v___x_2225_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3));
v___x_2226_ = l_Lean_addMacroScope(v_quotContext_2214_, v___x_2225_, v_currMacroScope_2215_);
v___x_2227_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__6));
lean_inc(v___x_2222_);
v___x_2228_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2222_);
lean_ctor_set(v___x_2228_, 1, v___x_2224_);
lean_ctor_set(v___x_2228_, 2, v___x_2226_);
lean_ctor_set(v___x_2228_, 3, v___x_2227_);
v___x_2229_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2230_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2231_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2222_);
v___x_2232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2222_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2222_);
v___x_2234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2222_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
lean_inc_ref(v___x_2234_);
lean_inc_ref(v___x_2232_);
lean_inc(v___x_2222_);
v___x_2235_ = l_Lean_Syntax_node3(v___x_2222_, v___x_2230_, v___x_2232_, v___x_2218_, v___x_2234_);
lean_inc(v___x_2222_);
v___x_2236_ = l_Lean_Syntax_node3(v___x_2222_, v___x_2230_, v___x_2232_, v___x_2220_, v___x_2234_);
lean_inc(v___x_2222_);
v___x_2237_ = l_Lean_Syntax_node2(v___x_2222_, v___x_2229_, v___x_2235_, v___x_2236_);
v___x_2238_ = l_Lean_Syntax_node2(v___x_2222_, v___x_2223_, v___x_2228_, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v_a_2209_);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure(lean_object* v_x_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2240_);
v___x_2244_ = l_Lean_Syntax_isOfKind(v_x_2240_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v_x_2240_);
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v_a_2242_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = l_Lean_Syntax_getArg(v_x_2240_, v___x_2247_);
lean_dec(v_x_2240_);
v___x_2249_ = l_Lean_Syntax_getNumArgs(v___x_2248_);
v___x_2250_ = lean_nat_dec_le(v___x_2247_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_a_2242_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v_ts_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = l_Lean_Syntax_getArg(v___x_2248_, v___x_2253_);
v___x_2255_ = l_Lean_Syntax_getArgs(v___x_2248_);
lean_dec(v___x_2248_);
v___x_2256_ = l_Array_extract___redArg(v___x_2255_, v___x_2247_, v___x_2249_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2258_ = lean_box(2);
v___x_2259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v___x_2257_);
lean_ctor_set(v___x_2259_, 2, v___x_2256_);
v_ts_2260_ = l_Lean_Syntax_getArgs(v___x_2259_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = lean_array_get_size(v_ts_2260_);
v___x_2262_ = lean_nat_dec_eq(v___x_2261_, v___x_2253_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2263_ = l_Lean_SourceInfo_fromRef(v_a_2241_, v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2265_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc(v___x_2263_);
v___x_2266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2263_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
lean_inc(v___x_2263_);
v___x_2268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2263_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
lean_inc(v___x_2263_);
v___x_2269_ = l_Lean_Syntax_node3(v___x_2263_, v___x_2264_, v___x_2266_, v___x_2254_, v___x_2268_);
v___x_2270_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2271_ = l_Array_append___redArg(v___x_2270_, v_ts_2260_);
lean_dec_ref(v_ts_2260_);
lean_inc(v___x_2263_);
v___x_2272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2263_);
lean_ctor_set(v___x_2272_, 1, v___x_2257_);
lean_ctor_set(v___x_2272_, 2, v___x_2271_);
v___x_2273_ = l_Lean_Syntax_node2(v___x_2263_, v___x_2243_, v___x_2269_, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v_a_2242_);
return v___x_2274_;
}
else
{
uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec_ref(v_ts_2260_);
v___x_2275_ = 0;
v___x_2276_ = l_Lean_SourceInfo_fromRef(v_a_2241_, v___x_2275_);
v___x_2277_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2278_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc(v___x_2276_);
v___x_2279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2276_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
lean_inc(v___x_2276_);
v___x_2281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2276_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = l_Lean_Syntax_node3(v___x_2276_, v___x_2277_, v___x_2279_, v___x_2254_, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v_a_2242_);
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure___boxed(lean_object* v_x_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Std_Do_SPred_Notation_unexpandPure(v_x_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2285_);
return v_res_2287_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = lean_box(0);
v___x_2302_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__5));
v___x_2303_ = l_Lean_addMacroScope(v___x_2302_, v___x_2301_, v___x_2300_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(lean_object* v_x_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
lean_inc(v_x_2330_);
v___x_2334_ = l_Lean_Syntax_isOfKind(v_x_2330_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
lean_inc(v_x_2330_);
v___x_2336_ = l_Lean_Syntax_isOfKind(v_x_2330_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__1));
lean_inc(v_x_2330_);
v___x_2338_ = l_Lean_Syntax_isOfKind(v_x_2330_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2339_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_2340_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v_x_2330_);
v___x_2341_ = l_Lean_Syntax_isOfKind(v_x_2330_, v___x_2340_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3));
lean_inc(v_x_2330_);
v___x_2343_ = l_Lean_Syntax_isOfKind(v_x_2330_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_x_2330_);
lean_ctor_set(v___x_2344_, 1, v___y_2332_);
return v___x_2344_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2345_);
v___x_2347_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_2346_);
v___x_2348_ = l_Lean_Syntax_isOfKind(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_dec(v___x_2346_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v_x_2330_);
lean_ctor_set(v___x_2349_, 1, v___y_2332_);
return v___x_2349_;
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = l_Lean_Syntax_getArg(v___x_2346_, v___x_2350_);
lean_dec(v___x_2346_);
v___x_2352_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_2351_);
v___x_2353_ = l_Lean_Syntax_isOfKind(v___x_2351_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec(v___x_2351_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_x_2330_);
lean_ctor_set(v___x_2354_, 1, v___y_2332_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2355_ = l_Lean_Syntax_getArg(v___x_2351_, v___x_2345_);
lean_dec(v___x_2351_);
v___x_2356_ = lean_box(0);
v___x_2357_ = l_Lean_Syntax_matchesIdent(v___x_2355_, v___x_2356_);
lean_dec(v___x_2355_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_x_2330_);
lean_ctor_set(v___x_2358_, 1, v___y_2332_);
return v___x_2358_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = lean_unsigned_to_nat(3u);
v___x_2360_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2359_);
lean_inc(v___x_2360_);
v___x_2361_ = l_Lean_Syntax_matchesNull(v___x_2360_, v___x_2350_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; 
lean_dec(v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_x_2330_);
lean_ctor_set(v___x_2362_, 1, v___y_2332_);
return v___x_2362_;
}
else
{
lean_object* v_P_2363_; lean_object* v___x_2364_; 
v_P_2363_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2350_);
lean_dec(v_x_2330_);
v___x_2364_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2363_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2390_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_a_2366_ = lean_ctor_get(v___x_2364_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2368_ = v___x_2364_;
v_isShared_2369_ = v_isSharedCheck_2390_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2390_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2370_ = l_Lean_Syntax_getArg(v___x_2360_, v___x_2345_);
lean_dec(v___x_2360_);
v___x_2371_ = l_Lean_SourceInfo_fromRef(v___y_2331_, v___x_2341_);
v___x_2372_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_2371_);
v___x_2373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2375_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_2376_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
lean_inc(v___x_2371_);
v___x_2377_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2371_);
lean_ctor_set(v___x_2377_, 1, v___x_2374_);
lean_ctor_set(v___x_2377_, 2, v___x_2375_);
lean_ctor_set(v___x_2377_, 3, v___x_2376_);
lean_inc(v___x_2371_);
v___x_2378_ = l_Lean_Syntax_node1(v___x_2371_, v___x_2352_, v___x_2377_);
lean_inc(v___x_2371_);
v___x_2379_ = l_Lean_Syntax_node2(v___x_2371_, v___x_2347_, v___x_2373_, v___x_2378_);
v___x_2380_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
lean_inc(v___x_2371_);
v___x_2381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2371_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
lean_inc(v___x_2371_);
v___x_2383_ = l_Lean_Syntax_node1(v___x_2371_, v___x_2382_, v___x_2370_);
v___x_2384_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2371_);
v___x_2385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2371_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = l_Lean_Syntax_node5(v___x_2371_, v___x_2342_, v___x_2379_, v_a_2365_, v___x_2381_, v___x_2383_, v___x_2385_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2386_);
v___x_2388_ = v___x_2368_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_a_2366_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
else
{
lean_dec(v___x_2360_);
return v___x_2364_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2391_);
v___x_2393_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_2392_);
v___x_2394_ = l_Lean_Syntax_isOfKind(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
lean_dec(v___x_2392_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_x_2330_);
lean_ctor_set(v___x_2395_, 1, v___y_2332_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = l_Lean_Syntax_getArg(v___x_2392_, v___x_2391_);
v___x_2398_ = l_Lean_Syntax_matchesNull(v___x_2397_, v___x_2396_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_dec(v___x_2392_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_x_2330_);
lean_ctor_set(v___x_2399_, 1, v___y_2332_);
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; lean_object* v_b_2401_; lean_object* v___x_2402_; 
lean_dec(v_x_2330_);
v___x_2400_ = lean_unsigned_to_nat(3u);
v_b_2401_ = l_Lean_Syntax_getArg(v___x_2392_, v___x_2400_);
v___x_2402_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_b_2401_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2424_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_a_2404_ = lean_ctor_get(v___x_2402_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2406_ = v___x_2402_;
v_isShared_2407_ = v_isSharedCheck_2424_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2424_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v_xs_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2408_ = l_Lean_Syntax_getArg(v___x_2392_, v___x_2396_);
lean_dec(v___x_2392_);
v_xs_2409_ = l_Lean_Syntax_getArgs(v___x_2408_);
lean_dec(v___x_2408_);
v___x_2410_ = l_Lean_SourceInfo_fromRef(v___y_2331_, v___x_2338_);
lean_inc(v___x_2410_);
v___x_2411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_2339_);
v___x_2412_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2413_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2414_ = l_Array_append___redArg(v___x_2413_, v_xs_2409_);
lean_dec_ref(v_xs_2409_);
lean_inc(v___x_2410_);
v___x_2415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2410_);
lean_ctor_set(v___x_2415_, 1, v___x_2412_);
lean_ctor_set(v___x_2415_, 2, v___x_2414_);
lean_inc(v___x_2410_);
v___x_2416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2410_);
lean_ctor_set(v___x_2416_, 1, v___x_2412_);
lean_ctor_set(v___x_2416_, 2, v___x_2413_);
v___x_2417_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
lean_inc(v___x_2410_);
v___x_2418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2410_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
lean_inc(v___x_2410_);
v___x_2419_ = l_Lean_Syntax_node4(v___x_2410_, v___x_2393_, v___x_2415_, v___x_2416_, v___x_2418_, v_a_2403_);
v___x_2420_ = l_Lean_Syntax_node2(v___x_2410_, v___x_2340_, v___x_2411_, v___x_2419_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2420_);
v___x_2422_ = v___x_2406_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_a_2404_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_dec(v___x_2392_);
return v___x_2402_;
}
}
}
}
}
else
{
lean_object* v___x_2425_; lean_object* v_t_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_unsigned_to_nat(3u);
v_t_2426_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2425_);
v___x_2427_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_t_2426_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2457_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_a_2429_ = lean_ctor_get(v___x_2427_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2431_ = v___x_2427_;
v_isShared_2432_ = v_isSharedCheck_2457_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2457_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v_e_2434_; lean_object* v___x_2435_; 
v___x_2433_ = lean_unsigned_to_nat(5u);
v_e_2434_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2433_);
v___x_2435_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_e_2434_, v___y_2331_, v_a_2429_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2456_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_a_2437_ = lean_ctor_get(v___x_2435_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2456_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2456_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2441_ = lean_unsigned_to_nat(1u);
v___x_2442_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2441_);
lean_dec(v_x_2330_);
v___x_2443_ = l_Lean_SourceInfo_fromRef(v___y_2331_, v___x_2336_);
v___x_2444_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__15));
lean_inc(v___x_2443_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 2);
lean_ctor_set(v___x_2431_, 1, v___x_2444_);
lean_ctor_set(v___x_2431_, 0, v___x_2443_);
v___x_2446_ = v___x_2431_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2447_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__16));
lean_inc(v___x_2443_);
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2443_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__17));
lean_inc(v___x_2443_);
v___x_2450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2443_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = l_Lean_Syntax_node6(v___x_2443_, v___x_2337_, v___x_2446_, v___x_2442_, v___x_2448_, v_a_2428_, v___x_2450_, v_a_2436_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2451_);
v___x_2453_ = v___x_2439_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_a_2437_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_del_object(v___x_2431_);
lean_dec(v_a_2428_);
lean_dec(v_x_2330_);
return v___x_2435_;
}
}
}
else
{
lean_dec(v_x_2330_);
return v___x_2427_;
}
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2458_ = lean_unsigned_to_nat(0u);
v___x_2459_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_2459_);
v___x_2461_ = l_Lean_Syntax_isOfKind(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
lean_dec(v___x_2459_);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_x_2330_);
lean_ctor_set(v___x_2462_, 1, v___y_2332_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = l_Lean_Syntax_getArg(v___x_2459_, v___x_2463_);
lean_dec(v___x_2459_);
v___x_2465_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_2464_);
v___x_2466_ = l_Lean_Syntax_isOfKind(v___x_2464_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; 
lean_dec(v___x_2464_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_x_2330_);
lean_ctor_set(v___x_2467_, 1, v___y_2332_);
return v___x_2467_;
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2468_ = l_Lean_Syntax_getArg(v___x_2464_, v___x_2458_);
lean_dec(v___x_2464_);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Lean_Syntax_matchesIdent(v___x_2468_, v___x_2469_);
lean_dec(v___x_2468_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_x_2330_);
lean_ctor_set(v___x_2471_, 1, v___y_2332_);
return v___x_2471_;
}
else
{
lean_object* v_P_2472_; lean_object* v___x_2473_; 
v_P_2472_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2463_);
lean_dec(v_x_2330_);
v___x_2473_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2472_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2494_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_a_2475_ = lean_ctor_get(v___x_2473_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2477_ = v___x_2473_;
v_isShared_2478_ = v_isSharedCheck_2494_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2494_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2479_ = l_Lean_SourceInfo_fromRef(v___y_2331_, v___x_2334_);
v___x_2480_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc(v___x_2479_);
v___x_2481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2483_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_2484_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
lean_inc(v___x_2479_);
v___x_2485_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2479_);
lean_ctor_set(v___x_2485_, 1, v___x_2482_);
lean_ctor_set(v___x_2485_, 2, v___x_2483_);
lean_ctor_set(v___x_2485_, 3, v___x_2484_);
lean_inc(v___x_2479_);
v___x_2486_ = l_Lean_Syntax_node1(v___x_2479_, v___x_2465_, v___x_2485_);
lean_inc(v___x_2479_);
v___x_2487_ = l_Lean_Syntax_node2(v___x_2479_, v___x_2460_, v___x_2481_, v___x_2486_);
v___x_2488_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2479_);
v___x_2489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2479_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = l_Lean_Syntax_node3(v___x_2479_, v___x_2335_, v___x_2487_, v_a_2474_, v___x_2489_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2490_);
v___x_2492_ = v___x_2477_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_a_2475_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
return v___x_2473_;
}
}
}
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2496_ = l_Lean_Syntax_getArg(v_x_2330_, v___x_2495_);
lean_dec(v_x_2330_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___y_2332_);
return v___x_2497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___boxed(lean_object* v_x_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_x_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2499_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails(lean_object* v_x_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___x_2506_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2503_);
v___x_2507_ = l_Lean_Syntax_isOfKind(v_x_2503_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec(v_x_2503_);
v___x_2508_ = lean_box(0);
v___x_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v_a_2505_);
return v___x_2509_;
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2510_ = lean_unsigned_to_nat(1u);
v___x_2511_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2510_);
lean_dec(v_x_2503_);
v___x_2512_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2511_);
v___x_2513_ = l_Lean_Syntax_matchesNull(v___x_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v_a_2505_);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; lean_object* v_P_2517_; lean_object* v___x_2518_; 
v___x_2516_ = lean_unsigned_to_nat(0u);
v_P_2517_ = l_Lean_Syntax_getArg(v___x_2511_, v___x_2516_);
v___x_2518_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2517_, v_a_2504_, v_a_2505_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v_a_2520_; lean_object* v_Q_2521_; lean_object* v___x_2522_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
v_a_2520_ = lean_ctor_get(v___x_2518_, 1);
lean_inc(v_a_2520_);
lean_dec_ref(v___x_2518_);
v_Q_2521_ = l_Lean_Syntax_getArg(v___x_2511_, v___x_2510_);
lean_dec(v___x_2511_);
v___x_2522_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2521_, v_a_2504_, v_a_2520_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2558_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_a_2524_ = lean_ctor_get(v___x_2522_, 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2526_ = v___x_2522_;
v_isShared_2527_ = v_isSharedCheck_2558_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2558_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
lean_inc(v_a_2519_);
v___x_2529_ = l_Lean_Syntax_isOfKind(v_a_2519_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2530_ = l_Lean_SourceInfo_fromRef(v_a_2504_, v___x_2529_);
v___x_2531_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_2532_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2530_);
v___x_2533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2530_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = l_Lean_Syntax_node3(v___x_2530_, v___x_2531_, v_a_2519_, v___x_2533_, v_a_2523_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2534_);
v___x_2536_ = v___x_2526_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_a_2524_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = l_Lean_Syntax_getArg(v_a_2519_, v___x_2510_);
v___x_2539_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_2540_ = l_Lean_Syntax_matchesIdent(v___x_2538_, v___x_2539_);
lean_dec(v___x_2538_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2541_ = l_Lean_SourceInfo_fromRef(v_a_2504_, v___x_2540_);
v___x_2542_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_2543_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2541_);
v___x_2544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2541_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node3(v___x_2541_, v___x_2542_, v_a_2519_, v___x_2544_, v_a_2523_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2545_);
v___x_2547_ = v___x_2526_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_a_2524_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
else
{
uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_dec(v_a_2519_);
v___x_2549_ = 0;
v___x_2550_ = l_Lean_SourceInfo_fromRef(v_a_2504_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
v___x_2552_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2550_);
v___x_2553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2550_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node2(v___x_2550_, v___x_2551_, v___x_2553_, v_a_2523_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2554_);
v___x_2556_ = v___x_2526_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_a_2524_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_a_2519_);
v_a_2559_ = lean_ctor_get(v___x_2522_, 0);
v_a_2560_ = lean_ctor_get(v___x_2522_, 1);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2522_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_inc(v_a_2559_);
lean_dec(v___x_2522_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2559_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v___x_2511_);
v_a_2568_ = lean_ctor_get(v___x_2518_, 0);
v_a_2569_ = lean_ctor_get(v___x_2518_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2518_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_inc(v_a_2568_);
lean_dec(v___x_2518_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2568_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails___boxed(lean_object* v_x_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Std_Do_SPred_Notation_unexpandEntails(v_x_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails(lean_object* v_x_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2585_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2582_);
v___x_2586_ = l_Lean_Syntax_isOfKind(v_x_2582_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec(v_x_2582_);
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v_a_2584_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2589_ = lean_unsigned_to_nat(1u);
v___x_2590_ = l_Lean_Syntax_getArg(v_x_2582_, v___x_2589_);
lean_dec(v_x_2582_);
v___x_2591_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2590_);
v___x_2592_ = l_Lean_Syntax_matchesNull(v___x_2590_, v___x_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_a_2584_);
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; lean_object* v_P_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_unsigned_to_nat(0u);
v_P_2596_ = l_Lean_Syntax_getArg(v___x_2590_, v___x_2595_);
v___x_2597_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2596_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_a_2599_; lean_object* v_Q_2600_; lean_object* v___x_2601_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
v_a_2599_ = lean_ctor_get(v___x_2597_, 1);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2597_);
v_Q_2600_ = l_Lean_Syntax_getArg(v___x_2590_, v___x_2589_);
lean_dec(v___x_2590_);
v___x_2601_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2600_, v_a_2583_, v_a_2599_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2616_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_a_2603_ = lean_ctor_get(v___x_2601_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2605_ = v___x_2601_;
v_isShared_2606_ = v_isSharedCheck_2616_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2616_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2607_ = 0;
v___x_2608_ = l_Lean_SourceInfo_fromRef(v_a_2583_, v___x_2607_);
v___x_2609_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
v___x_2610_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandBientails___closed__0));
lean_inc(v___x_2608_);
v___x_2611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2608_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = l_Lean_Syntax_node3(v___x_2608_, v___x_2609_, v_a_2598_, v___x_2611_, v_a_2602_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2612_);
v___x_2614_ = v___x_2605_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_a_2603_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v_a_2598_);
v_a_2617_ = lean_ctor_get(v___x_2601_, 0);
v_a_2618_ = lean_ctor_get(v___x_2601_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2601_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_inc(v_a_2617_);
lean_dec(v___x_2601_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2617_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v___x_2590_);
v_a_2626_ = lean_ctor_get(v___x_2597_, 0);
v_a_2627_ = lean_ctor_get(v___x_2597_, 1);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2597_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_inc(v_a_2626_);
lean_dec(v___x_2597_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2626_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails___boxed(lean_object* v_x_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Std_Do_SPred_Notation_unexpandBientails(v_x_2635_, v_a_2636_, v_a_2637_);
lean_dec(v_a_2636_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd(lean_object* v_x_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2640_);
v___x_2644_ = l_Lean_Syntax_isOfKind(v_x_2640_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec(v_x_2640_);
v___x_2645_ = lean_box(0);
v___x_2646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v_a_2642_);
return v___x_2646_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2647_ = lean_unsigned_to_nat(1u);
v___x_2648_ = l_Lean_Syntax_getArg(v_x_2640_, v___x_2647_);
lean_dec(v_x_2640_);
v___x_2649_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2648_);
v___x_2650_ = l_Lean_Syntax_matchesNull(v___x_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v_a_2642_);
return v___x_2652_;
}
else
{
lean_object* v___x_2653_; lean_object* v_P_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v_P_2654_ = l_Lean_Syntax_getArg(v___x_2648_, v___x_2653_);
v___x_2655_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2654_, v_a_2641_, v_a_2642_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v_a_2657_; lean_object* v_Q_2658_; lean_object* v___x_2659_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
v_a_2657_ = lean_ctor_get(v___x_2655_, 1);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2655_);
v_Q_2658_ = l_Lean_Syntax_getArg(v___x_2648_, v___x_2647_);
lean_dec(v___x_2648_);
v___x_2659_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2658_, v_a_2641_, v_a_2657_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2680_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_a_2661_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2663_ = v___x_2659_;
v_isShared_2664_ = v_isSharedCheck_2680_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2680_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2665_ = 0;
v___x_2666_ = l_Lean_SourceInfo_fromRef(v_a_2641_, v___x_2665_);
v___x_2667_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2668_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2666_);
v___x_2669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2666_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1));
v___x_2671_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandAnd___closed__0));
lean_inc(v___x_2666_);
v___x_2672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2666_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
lean_inc(v___x_2666_);
v___x_2673_ = l_Lean_Syntax_node3(v___x_2666_, v___x_2670_, v_a_2656_, v___x_2672_, v_a_2660_);
v___x_2674_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2666_);
v___x_2675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2666_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_Syntax_node3(v___x_2666_, v___x_2667_, v___x_2669_, v___x_2673_, v___x_2675_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2676_);
v___x_2678_ = v___x_2663_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_a_2661_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_a_2656_);
v_a_2681_ = lean_ctor_get(v___x_2659_, 0);
v_a_2682_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2659_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_inc(v_a_2681_);
lean_dec(v___x_2659_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2681_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v___x_2648_);
v_a_2690_ = lean_ctor_get(v___x_2655_, 0);
v_a_2691_ = lean_ctor_get(v___x_2655_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2655_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_inc(v_a_2690_);
lean_dec(v___x_2655_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2690_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd___boxed(lean_object* v_x_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Std_Do_SPred_Notation_unexpandAnd(v_x_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr(lean_object* v_x_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2704_);
v___x_2708_ = l_Lean_Syntax_isOfKind(v_x_2704_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec(v_x_2704_);
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v_a_2706_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2711_ = lean_unsigned_to_nat(1u);
v___x_2712_ = l_Lean_Syntax_getArg(v_x_2704_, v___x_2711_);
lean_dec(v_x_2704_);
v___x_2713_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2712_);
v___x_2714_ = l_Lean_Syntax_matchesNull(v___x_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v___x_2716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v_a_2706_);
return v___x_2716_;
}
else
{
lean_object* v___x_2717_; lean_object* v_P_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_unsigned_to_nat(0u);
v_P_2718_ = l_Lean_Syntax_getArg(v___x_2712_, v___x_2717_);
v___x_2719_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2718_, v_a_2705_, v_a_2706_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v_a_2721_; lean_object* v_Q_2722_; lean_object* v___x_2723_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
v_a_2721_ = lean_ctor_get(v___x_2719_, 1);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2719_);
v_Q_2722_ = l_Lean_Syntax_getArg(v___x_2712_, v___x_2711_);
lean_dec(v___x_2712_);
v___x_2723_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2722_, v_a_2705_, v_a_2721_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2744_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_a_2725_ = lean_ctor_get(v___x_2723_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2727_ = v___x_2723_;
v_isShared_2728_ = v_isSharedCheck_2744_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2744_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2729_ = 0;
v___x_2730_ = l_Lean_SourceInfo_fromRef(v_a_2705_, v___x_2729_);
v___x_2731_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2732_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2730_);
v___x_2733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2730_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3));
v___x_2735_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandOr___closed__0));
lean_inc(v___x_2730_);
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2730_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
lean_inc(v___x_2730_);
v___x_2737_ = l_Lean_Syntax_node3(v___x_2730_, v___x_2734_, v_a_2720_, v___x_2736_, v_a_2724_);
v___x_2738_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2730_);
v___x_2739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2730_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = l_Lean_Syntax_node3(v___x_2730_, v___x_2731_, v___x_2733_, v___x_2737_, v___x_2739_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2740_);
v___x_2742_ = v___x_2727_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_a_2725_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2720_);
v_a_2745_ = lean_ctor_get(v___x_2723_, 0);
v_a_2746_ = lean_ctor_get(v___x_2723_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2723_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_inc(v_a_2745_);
lean_dec(v___x_2723_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2745_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v___x_2712_);
v_a_2754_ = lean_ctor_get(v___x_2719_, 0);
v_a_2755_ = lean_ctor_get(v___x_2719_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2719_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_inc(v_a_2754_);
lean_dec(v___x_2719_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr___boxed(lean_object* v_x_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Std_Do_SPred_Notation_unexpandOr(v_x_2763_, v_a_2764_, v_a_2765_);
lean_dec(v_a_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot(lean_object* v_x_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2768_);
v___x_2772_ = l_Lean_Syntax_isOfKind(v_x_2768_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec(v_x_2768_);
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v_a_2770_);
return v___x_2774_;
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = l_Lean_Syntax_getArg(v_x_2768_, v___x_2775_);
lean_dec(v_x_2768_);
lean_inc(v___x_2776_);
v___x_2777_ = l_Lean_Syntax_matchesNull(v___x_2776_, v___x_2775_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec(v___x_2776_);
v___x_2778_ = lean_box(0);
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
lean_ctor_set(v___x_2779_, 1, v_a_2770_);
return v___x_2779_;
}
else
{
lean_object* v___x_2780_; lean_object* v_P_2781_; lean_object* v___x_2782_; 
v___x_2780_ = lean_unsigned_to_nat(0u);
v_P_2781_ = l_Lean_Syntax_getArg(v___x_2776_, v___x_2780_);
lean_dec(v___x_2776_);
v___x_2782_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2781_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2803_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_a_2784_ = lean_ctor_get(v___x_2782_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2786_ = v___x_2782_;
v_isShared_2787_ = v_isSharedCheck_2803_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2803_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2788_ = 0;
v___x_2789_ = l_Lean_SourceInfo_fromRef(v_a_2769_, v___x_2788_);
v___x_2790_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2791_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2789_);
v___x_2792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2789_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5));
v___x_2794_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandNot___closed__0));
lean_inc(v___x_2789_);
v___x_2795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2789_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
lean_inc(v___x_2789_);
v___x_2796_ = l_Lean_Syntax_node2(v___x_2789_, v___x_2793_, v___x_2795_, v_a_2783_);
v___x_2797_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2789_);
v___x_2798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2789_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = l_Lean_Syntax_node3(v___x_2789_, v___x_2790_, v___x_2792_, v___x_2796_, v___x_2798_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2799_);
v___x_2801_ = v___x_2786_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_a_2784_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_a_2804_ = lean_ctor_get(v___x_2782_, 0);
v_a_2805_ = lean_ctor_get(v___x_2782_, 1);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2782_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_inc(v_a_2804_);
lean_dec(v___x_2782_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2804_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot___boxed(lean_object* v_x_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Std_Do_SPred_Notation_unexpandNot(v_x_2813_, v_a_2814_, v_a_2815_);
lean_dec(v_a_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp(lean_object* v_x_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2818_);
v___x_2822_ = l_Lean_Syntax_isOfKind(v_x_2818_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v_x_2818_);
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
lean_ctor_set(v___x_2824_, 1, v_a_2820_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = l_Lean_Syntax_getArg(v_x_2818_, v___x_2825_);
lean_dec(v_x_2818_);
v___x_2827_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2826_);
v___x_2828_ = l_Lean_Syntax_matchesNull(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v_a_2820_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v_P_2832_; lean_object* v___x_2833_; 
v___x_2831_ = lean_unsigned_to_nat(0u);
v_P_2832_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2831_);
v___x_2833_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2832_, v_a_2819_, v_a_2820_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v_a_2835_; lean_object* v_Q_2836_; lean_object* v___x_2837_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
v_a_2835_ = lean_ctor_get(v___x_2833_, 1);
lean_inc(v_a_2835_);
lean_dec_ref(v___x_2833_);
v_Q_2836_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2825_);
lean_dec(v___x_2826_);
v___x_2837_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2836_, v_a_2819_, v_a_2835_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2858_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_a_2839_ = lean_ctor_get(v___x_2837_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2841_ = v___x_2837_;
v_isShared_2842_ = v_isSharedCheck_2858_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2858_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
uint8_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2843_ = 0;
v___x_2844_ = l_Lean_SourceInfo_fromRef(v_a_2819_, v___x_2843_);
v___x_2845_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2846_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2844_);
v___x_2847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2844_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7));
v___x_2849_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandImp___closed__0));
lean_inc(v___x_2844_);
v___x_2850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2844_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
lean_inc(v___x_2844_);
v___x_2851_ = l_Lean_Syntax_node3(v___x_2844_, v___x_2848_, v_a_2834_, v___x_2850_, v_a_2838_);
v___x_2852_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2844_);
v___x_2853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2844_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = l_Lean_Syntax_node3(v___x_2844_, v___x_2845_, v___x_2847_, v___x_2851_, v___x_2853_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2854_);
v___x_2856_ = v___x_2841_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_a_2839_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_a_2834_);
v_a_2859_ = lean_ctor_get(v___x_2837_, 0);
v_a_2860_ = lean_ctor_get(v___x_2837_, 1);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2837_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_inc(v_a_2859_);
lean_dec(v___x_2837_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2859_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v___x_2826_);
v_a_2868_ = lean_ctor_get(v___x_2833_, 0);
v_a_2869_ = lean_ctor_get(v___x_2833_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2833_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_inc(v_a_2868_);
lean_dec(v___x_2833_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2868_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp___boxed(lean_object* v_x_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Std_Do_SPred_Notation_unexpandImp(v_x_2877_, v_a_2878_, v_a_2879_);
lean_dec(v_a_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(size_t v_sz_2881_, size_t v_i_2882_, lean_object* v_bs_2883_){
_start:
{
uint8_t v___x_2884_; 
v___x_2884_ = lean_usize_dec_lt(v_i_2882_, v_sz_2881_);
if (v___x_2884_ == 0)
{
return v_bs_2883_;
}
else
{
lean_object* v_v_2885_; lean_object* v___x_2886_; lean_object* v_bs_x27_2887_; size_t v___x_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v_v_2885_ = lean_array_uget(v_bs_2883_, v_i_2882_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v_bs_x27_2887_ = lean_array_uset(v_bs_2883_, v_i_2882_, v___x_2886_);
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_add(v_i_2882_, v___x_2888_);
v___x_2890_ = lean_array_uset(v_bs_x27_2887_, v_i_2882_, v_v_2885_);
v_i_2882_ = v___x_2889_;
v_bs_2883_ = v___x_2890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1___boxed(lean_object* v_sz_2892_, lean_object* v_i_2893_, lean_object* v_bs_2894_){
_start:
{
size_t v_sz_boxed_2895_; size_t v_i_boxed_2896_; lean_object* v_res_2897_; 
v_sz_boxed_2895_ = lean_unbox_usize(v_sz_2892_);
lean_dec(v_sz_2892_);
v_i_boxed_2896_ = lean_unbox_usize(v_i_2893_);
lean_dec(v_i_2893_);
v_res_2897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_boxed_2895_, v_i_boxed_2896_, v_bs_2894_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(size_t v_sz_2898_, size_t v_i_2899_, lean_object* v_bs_2900_){
_start:
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_usize_dec_lt(v_i_2899_, v_sz_2898_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v_bs_2900_);
return v___x_2902_;
}
else
{
lean_object* v_v_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_v_2903_ = lean_array_uget(v_bs_2900_, v_i_2899_);
v___x_2904_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_v_2903_);
v___x_2905_ = l_Lean_Syntax_isOfKind(v_v_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_dec(v_v_2903_);
lean_dec_ref(v_bs_2900_);
v___x_2906_ = lean_box(0);
return v___x_2906_;
}
else
{
lean_object* v___x_2907_; lean_object* v_bs_x27_2908_; size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
v___x_2907_ = lean_unsigned_to_nat(0u);
v_bs_x27_2908_ = lean_array_uset(v_bs_2900_, v_i_2899_, v___x_2907_);
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_add(v_i_2899_, v___x_2909_);
v___x_2911_ = lean_array_uset(v_bs_x27_2908_, v_i_2899_, v_v_2903_);
v_i_2899_ = v___x_2910_;
v_bs_2900_ = v___x_2911_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0___boxed(lean_object* v_sz_2913_, lean_object* v_i_2914_, lean_object* v_bs_2915_){
_start:
{
size_t v_sz_boxed_2916_; size_t v_i_boxed_2917_; lean_object* v_res_2918_; 
v_sz_boxed_2916_ = lean_unbox_usize(v_sz_2913_);
lean_dec(v_sz_2913_);
v_i_boxed_2917_ = lean_unbox_usize(v_i_2914_);
lean_dec(v_i_2914_);
v_res_2918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_boxed_2916_, v_i_boxed_2917_, v_bs_2915_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall(lean_object* v_x_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2919_);
v___x_2923_ = l_Lean_Syntax_isOfKind(v_x_2919_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec(v_x_2919_);
v___x_2924_ = lean_box(0);
v___x_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v_a_2921_);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = l_Lean_Syntax_getArg(v_x_2919_, v___x_2926_);
lean_dec(v_x_2919_);
lean_inc(v___x_2927_);
v___x_2928_ = l_Lean_Syntax_matchesNull(v___x_2927_, v___x_2926_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v___x_2927_);
v___x_2929_ = lean_box(0);
v___x_2930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v_a_2921_);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = l_Lean_Syntax_getArg(v___x_2927_, v___x_2931_);
lean_dec(v___x_2927_);
v___x_2933_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_2932_);
v___x_2934_ = l_Lean_Syntax_isOfKind(v___x_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
lean_ctor_set(v___x_2936_, 1, v_a_2921_);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2937_ = l_Lean_Syntax_getArg(v___x_2932_, v___x_2926_);
lean_dec(v___x_2932_);
v___x_2938_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_2937_);
v___x_2939_ = l_Lean_Syntax_isOfKind(v___x_2937_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v_a_2921_);
return v___x_2941_;
}
else
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2942_ = l_Lean_Syntax_getArg(v___x_2937_, v___x_2931_);
lean_inc(v___x_2942_);
v___x_2943_ = l_Lean_Syntax_matchesNull(v___x_2942_, v___x_2926_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v___x_2942_);
lean_dec(v___x_2937_);
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v_a_2921_);
return v___x_2945_;
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2946_ = l_Lean_Syntax_getArg(v___x_2942_, v___x_2931_);
lean_dec(v___x_2942_);
v___x_2947_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_2946_);
v___x_2948_ = l_Lean_Syntax_isOfKind(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_dec(v___x_2946_);
lean_dec(v___x_2937_);
v___x_2949_ = lean_box(0);
v___x_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v_a_2921_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = l_Lean_Syntax_getArg(v___x_2937_, v___x_2926_);
v___x_2952_ = l_Lean_Syntax_matchesNull(v___x_2951_, v___x_2931_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec(v___x_2946_);
lean_dec(v___x_2937_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v_a_2921_);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; lean_object* v_00_u03a8_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2955_ = lean_unsigned_to_nat(3u);
v_00_u03a8_2956_ = l_Lean_Syntax_getArg(v___x_2937_, v___x_2955_);
lean_dec(v___x_2937_);
v___x_2957_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13));
lean_inc(v_00_u03a8_2956_);
v___x_2958_ = l_Lean_Syntax_isOfKind(v_00_u03a8_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2956_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2984_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_a_2961_ = lean_ctor_get(v___x_2959_, 1);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2963_ = v___x_2959_;
v_isShared_2964_ = v_isSharedCheck_2984_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2984_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2965_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_2958_);
v___x_2966_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2967_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_2965_);
v___x_2968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2965_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_2965_);
v___x_2970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2965_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
lean_inc(v___x_2965_);
v___x_2972_ = l_Lean_Syntax_node1(v___x_2965_, v___x_2971_, v___x_2946_);
v___x_2973_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_2965_);
v___x_2974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2965_);
lean_ctor_set(v___x_2974_, 1, v___x_2971_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
v___x_2975_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_2965_);
v___x_2976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2965_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
lean_inc(v___x_2965_);
v___x_2977_ = l_Lean_Syntax_node5(v___x_2965_, v___x_2957_, v___x_2970_, v___x_2972_, v___x_2974_, v___x_2976_, v_a_2960_);
v___x_2978_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_2965_);
v___x_2979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2965_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = l_Lean_Syntax_node3(v___x_2965_, v___x_2966_, v___x_2968_, v___x_2977_, v___x_2979_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2980_);
v___x_2982_ = v___x_2963_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_a_2961_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v___x_2946_);
v_a_2985_ = lean_ctor_get(v___x_2959_, 0);
v_a_2986_ = lean_ctor_get(v___x_2959_, 1);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2959_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_inc(v_a_2985_);
lean_dec(v___x_2959_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2985_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; 
v___x_2994_ = l_Lean_Syntax_getArg(v_00_u03a8_2956_, v___x_2926_);
v___x_2995_ = l_Lean_Syntax_getNumArgs(v___x_2994_);
v___x_2996_ = lean_nat_dec_le(v___x_2926_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; 
lean_dec(v___x_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2956_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3022_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_a_2999_ = lean_ctor_get(v___x_2997_, 1);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3001_ = v___x_2997_;
v_isShared_3002_ = v_isSharedCheck_3022_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3022_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3003_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_2996_);
v___x_3004_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3005_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3003_);
v___x_3006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3003_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_3003_);
v___x_3008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3003_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
lean_inc(v___x_3003_);
v___x_3010_ = l_Lean_Syntax_node1(v___x_3003_, v___x_3009_, v___x_2946_);
v___x_3011_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3003_);
v___x_3012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3003_);
lean_ctor_set(v___x_3012_, 1, v___x_3009_);
lean_ctor_set(v___x_3012_, 2, v___x_3011_);
v___x_3013_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3003_);
v___x_3014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3003_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
lean_inc(v___x_3003_);
v___x_3015_ = l_Lean_Syntax_node5(v___x_3003_, v___x_2957_, v___x_3008_, v___x_3010_, v___x_3012_, v___x_3014_, v_a_2998_);
v___x_3016_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3003_);
v___x_3017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3003_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = l_Lean_Syntax_node3(v___x_3003_, v___x_3004_, v___x_3006_, v___x_3015_, v___x_3017_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3018_);
v___x_3020_ = v___x_3001_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_a_2999_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v___x_2946_);
v_a_3023_ = lean_ctor_get(v___x_2997_, 0);
v_a_3024_ = lean_ctor_get(v___x_2997_, 1);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2997_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_inc(v_a_3023_);
lean_dec(v___x_2997_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3023_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = l_Lean_Syntax_getArg(v___x_2994_, v___x_2931_);
lean_inc(v___x_3032_);
v___x_3033_ = l_Lean_Syntax_isOfKind(v___x_3032_, v___x_2947_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; 
lean_dec(v___x_3032_);
lean_dec(v___x_2995_);
lean_dec(v___x_2994_);
v___x_3034_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2956_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3059_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_a_3036_ = lean_ctor_get(v___x_3034_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3038_ = v___x_3034_;
v_isShared_3039_ = v_isSharedCheck_3059_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3059_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3040_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_3033_);
v___x_3041_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3042_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3040_);
v___x_3043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3040_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_3040_);
v___x_3045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3040_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
lean_inc(v___x_3040_);
v___x_3047_ = l_Lean_Syntax_node1(v___x_3040_, v___x_3046_, v___x_2946_);
v___x_3048_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3040_);
v___x_3049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3040_);
lean_ctor_set(v___x_3049_, 1, v___x_3046_);
lean_ctor_set(v___x_3049_, 2, v___x_3048_);
v___x_3050_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3040_);
v___x_3051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3040_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
lean_inc(v___x_3040_);
v___x_3052_ = l_Lean_Syntax_node5(v___x_3040_, v___x_2957_, v___x_3045_, v___x_3047_, v___x_3049_, v___x_3051_, v_a_3035_);
v___x_3053_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3040_);
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3040_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = l_Lean_Syntax_node3(v___x_3040_, v___x_3041_, v___x_3043_, v___x_3052_, v___x_3054_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3055_);
v___x_3057_ = v___x_3038_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_a_3036_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v___x_2946_);
v_a_3060_ = lean_ctor_get(v___x_3034_, 0);
v_a_3061_ = lean_ctor_get(v___x_3034_, 1);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3034_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_inc(v_a_3060_);
lean_dec(v___x_3034_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3060_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; size_t v_sz_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3069_ = l_Lean_Syntax_getArgs(v___x_2994_);
lean_dec(v___x_2994_);
v___x_3070_ = l_Array_extract___redArg(v___x_3069_, v___x_2926_, v___x_2995_);
lean_dec_ref(v___x_3069_);
v___x_3071_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3072_ = lean_box(2);
v___x_3073_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3071_);
lean_ctor_set(v___x_3073_, 2, v___x_3070_);
v___x_3074_ = l_Lean_Syntax_getArgs(v___x_3073_);
lean_dec_ref(v___x_3073_);
v_sz_3075_ = lean_array_size(v___x_3074_);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_3075_, v___x_3076_, v___x_3074_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v___x_3078_; 
lean_dec(v___x_3032_);
v___x_3078_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2956_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3103_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_a_3080_ = lean_ctor_get(v___x_3078_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3082_ = v___x_3078_;
v_isShared_3083_ = v_isSharedCheck_3103_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3103_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3084_ = 0;
v___x_3085_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_3084_);
v___x_3086_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3087_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3085_);
v___x_3088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3085_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_3085_);
v___x_3090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3085_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
lean_inc(v___x_3085_);
v___x_3091_ = l_Lean_Syntax_node1(v___x_3085_, v___x_3071_, v___x_2946_);
v___x_3092_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3085_);
v___x_3093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3085_);
lean_ctor_set(v___x_3093_, 1, v___x_3071_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
v___x_3094_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3085_);
v___x_3095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3085_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
lean_inc(v___x_3085_);
v___x_3096_ = l_Lean_Syntax_node5(v___x_3085_, v___x_2957_, v___x_3090_, v___x_3091_, v___x_3093_, v___x_3095_, v_a_3079_);
v___x_3097_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3085_);
v___x_3098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3085_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_Syntax_node3(v___x_3085_, v___x_3086_, v___x_3088_, v___x_3096_, v___x_3098_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3099_);
v___x_3101_ = v___x_3082_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_a_3080_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v___x_2946_);
v_a_3104_ = lean_ctor_get(v___x_3078_, 0);
v_a_3105_ = lean_ctor_get(v___x_3078_, 1);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3078_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_inc(v_a_3104_);
lean_dec(v___x_3078_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3104_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_val_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v_val_3113_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_val_3113_);
lean_dec_ref(v___x_3077_);
v___x_3114_ = lean_unsigned_to_nat(2u);
v___x_3115_ = l_Lean_Syntax_getArg(v_00_u03a8_2956_, v___x_3114_);
v___x_3116_ = l_Lean_Syntax_matchesNull(v___x_3115_, v___x_2931_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; 
lean_dec(v_val_3113_);
lean_dec(v___x_3032_);
v___x_3117_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2956_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3141_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_a_3119_ = lean_ctor_get(v___x_3117_, 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3121_ = v___x_3117_;
v_isShared_3122_ = v_isSharedCheck_3141_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3141_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3123_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_3116_);
v___x_3124_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3125_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3123_);
v___x_3126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3123_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_3123_);
v___x_3128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3123_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
lean_inc(v___x_3123_);
v___x_3129_ = l_Lean_Syntax_node1(v___x_3123_, v___x_3071_, v___x_2946_);
v___x_3130_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3123_);
v___x_3131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3123_);
lean_ctor_set(v___x_3131_, 1, v___x_3071_);
lean_ctor_set(v___x_3131_, 2, v___x_3130_);
v___x_3132_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3123_);
v___x_3133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3123_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
lean_inc(v___x_3123_);
v___x_3134_ = l_Lean_Syntax_node5(v___x_3123_, v___x_2957_, v___x_3128_, v___x_3129_, v___x_3131_, v___x_3133_, v_a_3118_);
v___x_3135_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3123_);
v___x_3136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3123_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_Syntax_node3(v___x_3123_, v___x_3124_, v___x_3126_, v___x_3134_, v___x_3136_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3137_);
v___x_3139_ = v___x_3121_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v_a_3119_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v___x_2946_);
v_a_3142_ = lean_ctor_get(v___x_3117_, 0);
v_a_3143_ = lean_ctor_get(v___x_3117_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3117_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_inc(v_a_3142_);
lean_dec(v___x_3117_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3142_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v___x_3151_; lean_object* v_00_u03a8_3152_; lean_object* v___x_3153_; 
v___x_3151_ = lean_unsigned_to_nat(4u);
v_00_u03a8_3152_ = l_Lean_Syntax_getArg(v_00_u03a8_2956_, v___x_3151_);
lean_dec(v_00_u03a8_2956_);
v___x_3153_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3152_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3182_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_a_3155_ = lean_ctor_get(v___x_3153_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3157_ = v___x_3153_;
v_isShared_3158_ = v_isSharedCheck_3182_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3182_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; size_t v_sz_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3159_ = 0;
v___x_3160_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_3159_);
v___x_3161_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3162_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3160_);
v___x_3163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3160_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
lean_inc(v___x_3160_);
v___x_3165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3160_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = l_Array_mkArray2___redArg(v___x_2946_, v___x_3032_);
v_sz_3167_ = lean_array_size(v_val_3113_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_3167_, v___x_3076_, v_val_3113_);
v___x_3169_ = l_Array_append___redArg(v___x_3166_, v___x_3168_);
lean_dec_ref(v___x_3168_);
lean_inc(v___x_3160_);
v___x_3170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3160_);
lean_ctor_set(v___x_3170_, 1, v___x_3071_);
lean_ctor_set(v___x_3170_, 2, v___x_3169_);
v___x_3171_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3160_);
v___x_3172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3160_);
lean_ctor_set(v___x_3172_, 1, v___x_3071_);
lean_ctor_set(v___x_3172_, 2, v___x_3171_);
v___x_3173_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3160_);
v___x_3174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3160_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
lean_inc(v___x_3160_);
v___x_3175_ = l_Lean_Syntax_node5(v___x_3160_, v___x_2957_, v___x_3165_, v___x_3170_, v___x_3172_, v___x_3174_, v_a_3154_);
v___x_3176_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3160_);
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3160_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = l_Lean_Syntax_node3(v___x_3160_, v___x_3161_, v___x_3163_, v___x_3175_, v___x_3177_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3178_);
v___x_3180_ = v___x_3157_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_a_3155_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec(v_val_3113_);
lean_dec(v___x_3032_);
lean_dec(v___x_2946_);
v_a_3183_ = lean_ctor_get(v___x_3153_, 0);
v_a_3184_ = lean_ctor_get(v___x_3153_, 1);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3153_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_inc(v_a_3183_);
lean_dec(v___x_3153_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3183_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall___boxed(lean_object* v_x_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Std_Do_SPred_Notation_unexpandForall(v_x_3192_, v_a_3193_, v_a_3194_);
lean_dec(v_a_3193_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(lean_object* v___x_3200_, size_t v_sz_3201_, size_t v_i_3202_, lean_object* v_bs_3203_){
_start:
{
uint8_t v___x_3204_; 
v___x_3204_ = lean_usize_dec_lt(v_i_3202_, v_sz_3201_);
if (v___x_3204_ == 0)
{
lean_dec(v___x_3200_);
return v_bs_3203_;
}
else
{
lean_object* v___x_3205_; lean_object* v_v_3206_; lean_object* v___x_3207_; lean_object* v_bs_x27_3208_; lean_object* v___x_3209_; size_t v___x_3210_; size_t v___x_3211_; lean_object* v___x_3212_; 
v___x_3205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_3206_ = lean_array_uget(v_bs_3203_, v_i_3202_);
v___x_3207_ = lean_unsigned_to_nat(0u);
v_bs_x27_3208_ = lean_array_uset(v_bs_3203_, v_i_3202_, v___x_3207_);
lean_inc(v___x_3200_);
v___x_3209_ = l_Lean_Syntax_node1(v___x_3200_, v___x_3205_, v_v_3206_);
v___x_3210_ = ((size_t)1ULL);
v___x_3211_ = lean_usize_add(v_i_3202_, v___x_3210_);
v___x_3212_ = lean_array_uset(v_bs_x27_3208_, v_i_3202_, v___x_3209_);
v_i_3202_ = v___x_3211_;
v_bs_3203_ = v___x_3212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___boxed(lean_object* v___x_3214_, lean_object* v_sz_3215_, lean_object* v_i_3216_, lean_object* v_bs_3217_){
_start:
{
size_t v_sz_boxed_3218_; size_t v_i_boxed_3219_; lean_object* v_res_3220_; 
v_sz_boxed_3218_ = lean_unbox_usize(v_sz_3215_);
lean_dec(v_sz_3215_);
v_i_boxed_3219_ = lean_unbox_usize(v_i_3216_);
lean_dec(v_i_3216_);
v_res_3220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_3214_, v_sz_boxed_3218_, v_i_boxed_3219_, v_bs_3217_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(size_t v_sz_3221_, size_t v_i_3222_, lean_object* v_bs_3223_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_usize_dec_lt(v_i_3222_, v_sz_3221_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3225_, 0, v_bs_3223_);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; lean_object* v_v_3227_; uint8_t v___x_3228_; 
v___x_3226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_3227_ = lean_array_uget_borrowed(v_bs_3223_, v_i_3222_);
lean_inc(v_v_3227_);
v___x_3228_ = l_Lean_Syntax_isOfKind(v_v_3227_, v___x_3226_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_dec_ref(v_bs_3223_);
v___x_3229_ = lean_box(0);
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; lean_object* v_z_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3230_ = lean_unsigned_to_nat(0u);
v_z_3231_ = l_Lean_Syntax_getArg(v_v_3227_, v___x_3230_);
v___x_3232_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_z_3231_);
v___x_3233_ = l_Lean_Syntax_isOfKind(v_z_3231_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
lean_dec(v_z_3231_);
lean_dec_ref(v_bs_3223_);
v___x_3234_ = lean_box(0);
return v___x_3234_;
}
else
{
lean_object* v_bs_x27_3235_; size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; 
v_bs_x27_3235_ = lean_array_uset(v_bs_3223_, v_i_3222_, v___x_3230_);
v___x_3236_ = ((size_t)1ULL);
v___x_3237_ = lean_usize_add(v_i_3222_, v___x_3236_);
v___x_3238_ = lean_array_uset(v_bs_x27_3235_, v_i_3222_, v_z_3231_);
v_i_3222_ = v___x_3237_;
v_bs_3223_ = v___x_3238_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0___boxed(lean_object* v_sz_3240_, lean_object* v_i_3241_, lean_object* v_bs_3242_){
_start:
{
size_t v_sz_boxed_3243_; size_t v_i_boxed_3244_; lean_object* v_res_3245_; 
v_sz_boxed_3243_ = lean_unbox_usize(v_sz_3240_);
lean_dec(v_sz_3240_);
v_i_boxed_3244_ = lean_unbox_usize(v_i_3241_);
lean_dec(v_i_3241_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_boxed_3243_, v_i_boxed_3244_, v_bs_3242_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists(lean_object* v_x_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3251_);
v___x_3255_ = l_Lean_Syntax_isOfKind(v_x_3251_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_dec(v_x_3251_);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v_a_3253_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3258_ = lean_unsigned_to_nat(1u);
v___x_3259_ = l_Lean_Syntax_getArg(v_x_3251_, v___x_3258_);
lean_dec(v_x_3251_);
lean_inc(v___x_3259_);
v___x_3260_ = l_Lean_Syntax_matchesNull(v___x_3259_, v___x_3258_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v___x_3259_);
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v_a_3253_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = l_Lean_Syntax_getArg(v___x_3259_, v___x_3263_);
lean_dec(v___x_3259_);
v___x_3265_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_3264_);
v___x_3266_ = l_Lean_Syntax_isOfKind(v___x_3264_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec(v___x_3264_);
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
lean_ctor_set(v___x_3268_, 1, v_a_3253_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3269_ = l_Lean_Syntax_getArg(v___x_3264_, v___x_3258_);
lean_dec(v___x_3264_);
v___x_3270_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_3269_);
v___x_3271_ = l_Lean_Syntax_isOfKind(v___x_3269_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v___x_3273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
lean_ctor_set(v___x_3273_, 1, v_a_3253_);
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = l_Lean_Syntax_getArg(v___x_3269_, v___x_3263_);
lean_inc(v___x_3274_);
v___x_3275_ = l_Lean_Syntax_matchesNull(v___x_3274_, v___x_3258_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec(v___x_3274_);
lean_dec(v___x_3269_);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v_a_3253_);
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v___x_3278_ = l_Lean_Syntax_getArg(v___x_3274_, v___x_3263_);
lean_dec(v___x_3274_);
v___x_3279_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_3278_);
v___x_3280_ = l_Lean_Syntax_isOfKind(v___x_3278_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec(v___x_3278_);
lean_dec(v___x_3269_);
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v_a_3253_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3283_ = l_Lean_Syntax_getArg(v___x_3269_, v___x_3258_);
v___x_3284_ = l_Lean_Syntax_matchesNull(v___x_3283_, v___x_3263_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec(v___x_3278_);
lean_dec(v___x_3269_);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v_a_3253_);
return v___x_3286_;
}
else
{
lean_object* v___x_3287_; lean_object* v_00_u03a8_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3287_ = lean_unsigned_to_nat(3u);
v_00_u03a8_3288_ = l_Lean_Syntax_getArg(v___x_3269_, v___x_3287_);
lean_dec(v___x_3269_);
v___x_3289_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11));
lean_inc(v_00_u03a8_3288_);
v___x_3290_ = l_Lean_Syntax_isOfKind(v_00_u03a8_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3322_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_a_3293_ = lean_ctor_get(v___x_3291_, 1);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3295_ = v___x_3291_;
v_isShared_3296_ = v_isSharedCheck_3322_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3322_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3297_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3290_);
v___x_3298_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3299_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3297_);
v___x_3300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3297_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3297_);
v___x_3302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3297_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
v___x_3304_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_3305_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_3297_);
v___x_3307_ = l_Lean_Syntax_node1(v___x_3297_, v___x_3306_, v___x_3278_);
lean_inc(v___x_3297_);
v___x_3308_ = l_Lean_Syntax_node1(v___x_3297_, v___x_3305_, v___x_3307_);
v___x_3309_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3297_);
v___x_3310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3297_);
lean_ctor_set(v___x_3310_, 1, v___x_3305_);
lean_ctor_set(v___x_3310_, 2, v___x_3309_);
lean_inc(v___x_3297_);
v___x_3311_ = l_Lean_Syntax_node2(v___x_3297_, v___x_3304_, v___x_3308_, v___x_3310_);
lean_inc(v___x_3297_);
v___x_3312_ = l_Lean_Syntax_node1(v___x_3297_, v___x_3303_, v___x_3311_);
v___x_3313_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3297_);
v___x_3314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3297_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
lean_inc(v___x_3297_);
v___x_3315_ = l_Lean_Syntax_node4(v___x_3297_, v___x_3289_, v___x_3302_, v___x_3312_, v___x_3314_, v_a_3292_);
v___x_3316_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3297_);
v___x_3317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3297_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___x_3318_ = l_Lean_Syntax_node3(v___x_3297_, v___x_3298_, v___x_3300_, v___x_3315_, v___x_3317_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3318_);
v___x_3320_ = v___x_3295_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_a_3293_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec(v___x_3278_);
v_a_3323_ = lean_ctor_get(v___x_3291_, 0);
v_a_3324_ = lean_ctor_get(v___x_3291_, 1);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3291_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_inc(v_a_3323_);
lean_dec(v___x_3291_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3323_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3332_ = l_Lean_Syntax_getArg(v_00_u03a8_3288_, v___x_3258_);
v___x_3333_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
lean_inc(v___x_3332_);
v___x_3334_ = l_Lean_Syntax_isOfKind(v___x_3332_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
lean_dec(v___x_3332_);
v___x_3335_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3365_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_a_3337_ = lean_ctor_get(v___x_3335_, 1);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3339_ = v___x_3335_;
v_isShared_3340_ = v_isSharedCheck_3365_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3365_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3341_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3334_);
v___x_3342_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3343_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3341_);
v___x_3344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3341_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3341_);
v___x_3346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3341_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_3348_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_3341_);
v___x_3350_ = l_Lean_Syntax_node1(v___x_3341_, v___x_3349_, v___x_3278_);
lean_inc(v___x_3341_);
v___x_3351_ = l_Lean_Syntax_node1(v___x_3341_, v___x_3348_, v___x_3350_);
v___x_3352_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3341_);
v___x_3353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3341_);
lean_ctor_set(v___x_3353_, 1, v___x_3348_);
lean_ctor_set(v___x_3353_, 2, v___x_3352_);
lean_inc(v___x_3341_);
v___x_3354_ = l_Lean_Syntax_node2(v___x_3341_, v___x_3347_, v___x_3351_, v___x_3353_);
lean_inc(v___x_3341_);
v___x_3355_ = l_Lean_Syntax_node1(v___x_3341_, v___x_3333_, v___x_3354_);
v___x_3356_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3341_);
v___x_3357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3341_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
lean_inc(v___x_3341_);
v___x_3358_ = l_Lean_Syntax_node4(v___x_3341_, v___x_3289_, v___x_3346_, v___x_3355_, v___x_3357_, v_a_3336_);
v___x_3359_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3341_);
v___x_3360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3341_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_Syntax_node3(v___x_3341_, v___x_3342_, v___x_3344_, v___x_3358_, v___x_3360_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3361_);
v___x_3363_ = v___x_3339_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_a_3337_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec(v___x_3278_);
v_a_3366_ = lean_ctor_get(v___x_3335_, 0);
v_a_3367_ = lean_ctor_get(v___x_3335_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3335_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_inc(v_a_3366_);
lean_dec(v___x_3335_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3366_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v___x_3375_ = l_Lean_Syntax_getArg(v___x_3332_, v___x_3263_);
lean_dec(v___x_3332_);
v___x_3376_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
lean_inc(v___x_3375_);
v___x_3377_ = l_Lean_Syntax_isOfKind(v___x_3375_, v___x_3376_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; 
lean_dec(v___x_3375_);
v___x_3378_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3407_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_a_3380_ = lean_ctor_get(v___x_3378_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3382_ = v___x_3378_;
v_isShared_3383_ = v_isSharedCheck_3407_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3407_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3384_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3377_);
v___x_3385_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3386_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3384_);
v___x_3387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3384_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3384_);
v___x_3389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3384_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_3384_);
v___x_3392_ = l_Lean_Syntax_node1(v___x_3384_, v___x_3391_, v___x_3278_);
lean_inc(v___x_3384_);
v___x_3393_ = l_Lean_Syntax_node1(v___x_3384_, v___x_3390_, v___x_3392_);
v___x_3394_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3384_);
v___x_3395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3384_);
lean_ctor_set(v___x_3395_, 1, v___x_3390_);
lean_ctor_set(v___x_3395_, 2, v___x_3394_);
lean_inc(v___x_3384_);
v___x_3396_ = l_Lean_Syntax_node2(v___x_3384_, v___x_3376_, v___x_3393_, v___x_3395_);
lean_inc(v___x_3384_);
v___x_3397_ = l_Lean_Syntax_node1(v___x_3384_, v___x_3333_, v___x_3396_);
v___x_3398_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3384_);
v___x_3399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3384_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
lean_inc(v___x_3384_);
v___x_3400_ = l_Lean_Syntax_node4(v___x_3384_, v___x_3289_, v___x_3389_, v___x_3397_, v___x_3399_, v_a_3379_);
v___x_3401_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3384_);
v___x_3402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3384_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = l_Lean_Syntax_node3(v___x_3384_, v___x_3385_, v___x_3387_, v___x_3400_, v___x_3402_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3403_);
v___x_3405_ = v___x_3382_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_a_3380_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v___x_3278_);
v_a_3408_ = lean_ctor_get(v___x_3378_, 0);
v_a_3409_ = lean_ctor_get(v___x_3378_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3378_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_inc(v_a_3408_);
lean_dec(v___x_3378_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3408_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3417_ = l_Lean_Syntax_getArg(v___x_3375_, v___x_3263_);
v___x_3418_ = l_Lean_Syntax_getNumArgs(v___x_3417_);
v___x_3419_ = lean_nat_dec_le(v___x_3258_, v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; 
lean_dec(v___x_3418_);
lean_dec(v___x_3417_);
lean_dec(v___x_3375_);
v___x_3420_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3449_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_a_3422_ = lean_ctor_get(v___x_3420_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3424_ = v___x_3420_;
v_isShared_3425_ = v_isSharedCheck_3449_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3449_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3426_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3419_);
v___x_3427_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3428_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3426_);
v___x_3429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3426_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3426_);
v___x_3431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3426_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_3426_);
v___x_3434_ = l_Lean_Syntax_node1(v___x_3426_, v___x_3433_, v___x_3278_);
lean_inc(v___x_3426_);
v___x_3435_ = l_Lean_Syntax_node1(v___x_3426_, v___x_3432_, v___x_3434_);
v___x_3436_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3426_);
v___x_3437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3426_);
lean_ctor_set(v___x_3437_, 1, v___x_3432_);
lean_ctor_set(v___x_3437_, 2, v___x_3436_);
lean_inc(v___x_3426_);
v___x_3438_ = l_Lean_Syntax_node2(v___x_3426_, v___x_3376_, v___x_3435_, v___x_3437_);
lean_inc(v___x_3426_);
v___x_3439_ = l_Lean_Syntax_node1(v___x_3426_, v___x_3333_, v___x_3438_);
v___x_3440_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3426_);
v___x_3441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3426_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
lean_inc(v___x_3426_);
v___x_3442_ = l_Lean_Syntax_node4(v___x_3426_, v___x_3289_, v___x_3431_, v___x_3439_, v___x_3441_, v_a_3421_);
v___x_3443_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3426_);
v___x_3444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3426_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = l_Lean_Syntax_node3(v___x_3426_, v___x_3427_, v___x_3429_, v___x_3442_, v___x_3444_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3445_);
v___x_3447_ = v___x_3424_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_a_3422_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v___x_3278_);
v_a_3450_ = lean_ctor_get(v___x_3420_, 0);
v_a_3451_ = lean_ctor_get(v___x_3420_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3420_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_inc(v_a_3450_);
lean_dec(v___x_3420_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3450_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3459_ = l_Lean_Syntax_getArg(v___x_3417_, v___x_3263_);
v___x_3460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_3459_);
v___x_3461_ = l_Lean_Syntax_isOfKind(v___x_3459_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
lean_dec(v___x_3459_);
lean_dec(v___x_3418_);
lean_dec(v___x_3417_);
lean_dec(v___x_3375_);
v___x_3462_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3490_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_a_3464_ = lean_ctor_get(v___x_3462_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3466_ = v___x_3462_;
v_isShared_3467_ = v_isSharedCheck_3490_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3490_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3468_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3461_);
v___x_3469_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3470_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3468_);
v___x_3471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3468_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3468_);
v___x_3473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3468_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
lean_inc(v___x_3468_);
v___x_3475_ = l_Lean_Syntax_node1(v___x_3468_, v___x_3460_, v___x_3278_);
lean_inc(v___x_3468_);
v___x_3476_ = l_Lean_Syntax_node1(v___x_3468_, v___x_3474_, v___x_3475_);
v___x_3477_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3468_);
v___x_3478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3468_);
lean_ctor_set(v___x_3478_, 1, v___x_3474_);
lean_ctor_set(v___x_3478_, 2, v___x_3477_);
lean_inc(v___x_3468_);
v___x_3479_ = l_Lean_Syntax_node2(v___x_3468_, v___x_3376_, v___x_3476_, v___x_3478_);
lean_inc(v___x_3468_);
v___x_3480_ = l_Lean_Syntax_node1(v___x_3468_, v___x_3333_, v___x_3479_);
v___x_3481_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3468_);
v___x_3482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3468_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
lean_inc(v___x_3468_);
v___x_3483_ = l_Lean_Syntax_node4(v___x_3468_, v___x_3289_, v___x_3473_, v___x_3480_, v___x_3482_, v_a_3463_);
v___x_3484_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3468_);
v___x_3485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3468_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = l_Lean_Syntax_node3(v___x_3468_, v___x_3469_, v___x_3471_, v___x_3483_, v___x_3485_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3486_);
v___x_3488_ = v___x_3466_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_a_3464_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec(v___x_3278_);
v_a_3491_ = lean_ctor_get(v___x_3462_, 0);
v_a_3492_ = lean_ctor_get(v___x_3462_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3462_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_inc(v_a_3491_);
lean_dec(v___x_3462_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3491_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v___x_3500_; uint8_t v___x_3501_; 
v___x_3500_ = l_Lean_Syntax_getArg(v___x_3459_, v___x_3263_);
lean_dec(v___x_3459_);
lean_inc(v___x_3500_);
v___x_3501_ = l_Lean_Syntax_isOfKind(v___x_3500_, v___x_3279_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v___x_3500_);
lean_dec(v___x_3418_);
lean_dec(v___x_3417_);
lean_dec(v___x_3375_);
v___x_3502_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3530_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_a_3504_ = lean_ctor_get(v___x_3502_, 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3506_ = v___x_3502_;
v_isShared_3507_ = v_isSharedCheck_3530_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3530_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3508_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3501_);
v___x_3509_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3510_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3508_);
v___x_3511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3508_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3508_);
v___x_3513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3508_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
lean_inc(v___x_3508_);
v___x_3515_ = l_Lean_Syntax_node1(v___x_3508_, v___x_3460_, v___x_3278_);
lean_inc(v___x_3508_);
v___x_3516_ = l_Lean_Syntax_node1(v___x_3508_, v___x_3514_, v___x_3515_);
v___x_3517_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3508_);
v___x_3518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3508_);
lean_ctor_set(v___x_3518_, 1, v___x_3514_);
lean_ctor_set(v___x_3518_, 2, v___x_3517_);
lean_inc(v___x_3508_);
v___x_3519_ = l_Lean_Syntax_node2(v___x_3508_, v___x_3376_, v___x_3516_, v___x_3518_);
lean_inc(v___x_3508_);
v___x_3520_ = l_Lean_Syntax_node1(v___x_3508_, v___x_3333_, v___x_3519_);
v___x_3521_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3508_);
v___x_3522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3508_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
lean_inc(v___x_3508_);
v___x_3523_ = l_Lean_Syntax_node4(v___x_3508_, v___x_3289_, v___x_3513_, v___x_3520_, v___x_3522_, v_a_3503_);
v___x_3524_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3508_);
v___x_3525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3508_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l_Lean_Syntax_node3(v___x_3508_, v___x_3509_, v___x_3511_, v___x_3523_, v___x_3525_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3526_);
v___x_3528_ = v___x_3506_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_a_3504_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v___x_3278_);
v_a_3531_ = lean_ctor_get(v___x_3502_, 0);
v_a_3532_ = lean_ctor_get(v___x_3502_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3502_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_inc(v_a_3531_);
lean_dec(v___x_3502_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3531_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; size_t v_sz_3546_; size_t v___x_3547_; lean_object* v___x_3548_; 
v___x_3540_ = l_Lean_Syntax_getArgs(v___x_3417_);
lean_dec(v___x_3417_);
v___x_3541_ = l_Array_extract___redArg(v___x_3540_, v___x_3258_, v___x_3418_);
lean_dec_ref(v___x_3540_);
v___x_3542_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3543_ = lean_box(2);
v___x_3544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v___x_3542_);
lean_ctor_set(v___x_3544_, 2, v___x_3541_);
v___x_3545_ = l_Lean_Syntax_getArgs(v___x_3544_);
lean_dec_ref(v___x_3544_);
v_sz_3546_ = lean_array_size(v___x_3545_);
v___x_3547_ = ((size_t)0ULL);
v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_3546_, v___x_3547_, v___x_3545_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; 
lean_dec(v___x_3500_);
lean_dec(v___x_3375_);
v___x_3549_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3577_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_a_3551_ = lean_ctor_get(v___x_3549_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3553_ = v___x_3549_;
v_isShared_3554_ = v_isSharedCheck_3577_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3577_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3555_ = 0;
v___x_3556_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3555_);
v___x_3557_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3558_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3556_);
v___x_3559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3556_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3556_);
v___x_3561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3556_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
lean_inc(v___x_3556_);
v___x_3562_ = l_Lean_Syntax_node1(v___x_3556_, v___x_3460_, v___x_3278_);
lean_inc(v___x_3556_);
v___x_3563_ = l_Lean_Syntax_node1(v___x_3556_, v___x_3542_, v___x_3562_);
v___x_3564_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3556_);
v___x_3565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3556_);
lean_ctor_set(v___x_3565_, 1, v___x_3542_);
lean_ctor_set(v___x_3565_, 2, v___x_3564_);
lean_inc(v___x_3556_);
v___x_3566_ = l_Lean_Syntax_node2(v___x_3556_, v___x_3376_, v___x_3563_, v___x_3565_);
lean_inc(v___x_3556_);
v___x_3567_ = l_Lean_Syntax_node1(v___x_3556_, v___x_3333_, v___x_3566_);
v___x_3568_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3556_);
v___x_3569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3556_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
lean_inc(v___x_3556_);
v___x_3570_ = l_Lean_Syntax_node4(v___x_3556_, v___x_3289_, v___x_3561_, v___x_3567_, v___x_3569_, v_a_3550_);
v___x_3571_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3556_);
v___x_3572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3556_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_Syntax_node3(v___x_3556_, v___x_3557_, v___x_3559_, v___x_3570_, v___x_3572_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3573_);
v___x_3575_ = v___x_3553_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_a_3551_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v___x_3278_);
v_a_3578_ = lean_ctor_get(v___x_3549_, 0);
v_a_3579_ = lean_ctor_get(v___x_3549_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3549_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_inc(v_a_3578_);
lean_dec(v___x_3549_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3578_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_val_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v_val_3587_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_val_3587_);
lean_dec_ref(v___x_3548_);
v___x_3588_ = l_Lean_Syntax_getArg(v___x_3375_, v___x_3258_);
lean_dec(v___x_3375_);
v___x_3589_ = l_Lean_Syntax_matchesNull(v___x_3588_, v___x_3263_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; 
lean_dec(v_val_3587_);
lean_dec(v___x_3500_);
v___x_3590_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3288_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3617_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_a_3592_ = lean_ctor_get(v___x_3590_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3594_ = v___x_3590_;
v_isShared_3595_ = v_isSharedCheck_3617_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3617_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3596_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3589_);
v___x_3597_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3598_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3596_);
v___x_3599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3596_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3596_);
v___x_3601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3596_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
lean_inc(v___x_3596_);
v___x_3602_ = l_Lean_Syntax_node1(v___x_3596_, v___x_3460_, v___x_3278_);
lean_inc(v___x_3596_);
v___x_3603_ = l_Lean_Syntax_node1(v___x_3596_, v___x_3542_, v___x_3602_);
v___x_3604_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3596_);
v___x_3605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3596_);
lean_ctor_set(v___x_3605_, 1, v___x_3542_);
lean_ctor_set(v___x_3605_, 2, v___x_3604_);
lean_inc(v___x_3596_);
v___x_3606_ = l_Lean_Syntax_node2(v___x_3596_, v___x_3376_, v___x_3603_, v___x_3605_);
lean_inc(v___x_3596_);
v___x_3607_ = l_Lean_Syntax_node1(v___x_3596_, v___x_3333_, v___x_3606_);
v___x_3608_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3596_);
v___x_3609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3596_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
lean_inc(v___x_3596_);
v___x_3610_ = l_Lean_Syntax_node4(v___x_3596_, v___x_3289_, v___x_3601_, v___x_3607_, v___x_3609_, v_a_3591_);
v___x_3611_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3596_);
v___x_3612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3596_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l_Lean_Syntax_node3(v___x_3596_, v___x_3597_, v___x_3599_, v___x_3610_, v___x_3612_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v___x_3613_);
v___x_3615_ = v___x_3594_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_a_3592_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec(v___x_3278_);
v_a_3618_ = lean_ctor_get(v___x_3590_, 0);
v_a_3619_ = lean_ctor_get(v___x_3590_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3590_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_inc(v_a_3618_);
lean_dec(v___x_3590_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3618_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_00_u03a8_3627_; lean_object* v___x_3628_; 
v_00_u03a8_3627_ = l_Lean_Syntax_getArg(v_00_u03a8_3288_, v___x_3287_);
lean_dec(v_00_u03a8_3288_);
v___x_3628_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3627_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3661_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_a_3630_ = lean_ctor_get(v___x_3628_, 1);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3632_ = v___x_3628_;
v_isShared_3633_ = v_isSharedCheck_3661_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3661_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
uint8_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; size_t v_sz_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3634_ = 0;
v___x_3635_ = l_Lean_SourceInfo_fromRef(v_a_3252_, v___x_3634_);
v___x_3636_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3637_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3635_);
v___x_3638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3635_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
lean_inc(v___x_3635_);
v___x_3640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3635_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
lean_inc(v___x_3635_);
v___x_3641_ = l_Lean_Syntax_node1(v___x_3635_, v___x_3460_, v___x_3278_);
lean_inc(v___x_3635_);
v___x_3642_ = l_Lean_Syntax_node1(v___x_3635_, v___x_3460_, v___x_3500_);
v___x_3643_ = l_Array_mkArray2___redArg(v___x_3641_, v___x_3642_);
v_sz_3644_ = lean_array_size(v_val_3587_);
lean_inc(v___x_3635_);
v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_3635_, v_sz_3644_, v___x_3547_, v_val_3587_);
v___x_3646_ = l_Array_append___redArg(v___x_3643_, v___x_3645_);
lean_dec_ref(v___x_3645_);
lean_inc(v___x_3635_);
v___x_3647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3635_);
lean_ctor_set(v___x_3647_, 1, v___x_3542_);
lean_ctor_set(v___x_3647_, 2, v___x_3646_);
v___x_3648_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
lean_inc(v___x_3635_);
v___x_3649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3635_);
lean_ctor_set(v___x_3649_, 1, v___x_3542_);
lean_ctor_set(v___x_3649_, 2, v___x_3648_);
lean_inc(v___x_3635_);
v___x_3650_ = l_Lean_Syntax_node2(v___x_3635_, v___x_3376_, v___x_3647_, v___x_3649_);
lean_inc(v___x_3635_);
v___x_3651_ = l_Lean_Syntax_node1(v___x_3635_, v___x_3333_, v___x_3650_);
v___x_3652_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
lean_inc(v___x_3635_);
v___x_3653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3635_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
lean_inc(v___x_3635_);
v___x_3654_ = l_Lean_Syntax_node4(v___x_3635_, v___x_3289_, v___x_3640_, v___x_3651_, v___x_3653_, v_a_3629_);
v___x_3655_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3635_);
v___x_3656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3635_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l_Lean_Syntax_node3(v___x_3635_, v___x_3636_, v___x_3638_, v___x_3654_, v___x_3656_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3657_);
v___x_3659_ = v___x_3632_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_a_3630_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v_val_3587_);
lean_dec(v___x_3500_);
lean_dec(v___x_3278_);
v_a_3662_ = lean_ctor_get(v___x_3628_, 0);
v_a_3663_ = lean_ctor_get(v___x_3628_, 1);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3628_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_inc(v_a_3662_);
lean_dec(v___x_3628_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3662_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists___boxed(lean_object* v_x_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Std_Do_SPred_Notation_unexpandExists(v_x_3671_, v_a_3672_, v_a_3673_);
lean_dec(v_a_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff(lean_object* v_x_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3679_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3676_);
v___x_3680_ = l_Lean_Syntax_isOfKind(v_x_3676_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec(v_x_3676_);
v___x_3681_ = lean_box(0);
v___x_3682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v_a_3678_);
return v___x_3682_;
}
else
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3683_ = lean_unsigned_to_nat(1u);
v___x_3684_ = l_Lean_Syntax_getArg(v_x_3676_, v___x_3683_);
lean_dec(v_x_3676_);
v___x_3685_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3684_);
v___x_3686_ = l_Lean_Syntax_matchesNull(v___x_3684_, v___x_3685_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v___x_3688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v_a_3678_);
return v___x_3688_;
}
else
{
lean_object* v___x_3689_; lean_object* v_P_3690_; lean_object* v___x_3691_; 
v___x_3689_ = lean_unsigned_to_nat(0u);
v_P_3690_ = l_Lean_Syntax_getArg(v___x_3684_, v___x_3689_);
v___x_3691_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_3690_, v_a_3677_, v_a_3678_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v_a_3693_; lean_object* v_Q_3694_; lean_object* v___x_3695_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
v_a_3693_ = lean_ctor_get(v___x_3691_, 1);
lean_inc(v_a_3693_);
lean_dec_ref(v___x_3691_);
v_Q_3694_ = l_Lean_Syntax_getArg(v___x_3684_, v___x_3683_);
lean_dec(v___x_3684_);
v___x_3695_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_3694_, v_a_3677_, v_a_3693_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3716_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_a_3697_ = lean_ctor_get(v___x_3695_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3699_ = v___x_3695_;
v_isShared_3700_ = v_isSharedCheck_3716_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3716_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
uint8_t v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
v___x_3701_ = 0;
v___x_3702_ = l_Lean_SourceInfo_fromRef(v_a_3677_, v___x_3701_);
v___x_3703_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3704_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc(v___x_3702_);
v___x_3705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3702_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9));
v___x_3707_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandIff___closed__0));
lean_inc(v___x_3702_);
v___x_3708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3702_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
lean_inc(v___x_3702_);
v___x_3709_ = l_Lean_Syntax_node3(v___x_3702_, v___x_3706_, v_a_3692_, v___x_3708_, v_a_3696_);
v___x_3710_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
lean_inc(v___x_3702_);
v___x_3711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3702_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = l_Lean_Syntax_node3(v___x_3702_, v___x_3703_, v___x_3705_, v___x_3709_, v___x_3711_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3712_);
v___x_3714_ = v___x_3699_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_a_3697_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec(v_a_3692_);
v_a_3717_ = lean_ctor_get(v___x_3695_, 0);
v_a_3718_ = lean_ctor_get(v___x_3695_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3695_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_inc(v_a_3717_);
lean_dec(v___x_3695_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3717_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v___x_3684_);
v_a_3726_ = lean_ctor_get(v___x_3691_, 0);
v_a_3727_ = lean_ctor_get(v___x_3691_, 1);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3691_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_inc(v_a_3726_);
lean_dec(v___x_3691_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3726_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff___boxed(lean_object* v_x_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_Std_Do_SPred_Notation_unexpandIff(v_x_3735_, v_a_3736_, v_a_3737_);
lean_dec(v_a_3736_);
return v_res_3738_;
}
}
lean_object* runtime_initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_SPred_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_SPred_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_SPred_Notation(builtin);
}
#ifdef __cplusplus
}
#endif
