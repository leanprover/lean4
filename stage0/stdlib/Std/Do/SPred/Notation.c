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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___boxed(lean_object*, lean_object*, lean_object*);
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
v_currMacroScope_135_ = lean_ctor_get(v_a_128_, 2);
v_ref_136_ = lean_ctor_get(v_a_128_, 5);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = l_Lean_Syntax_getArg(v_x_127_, v___x_137_);
lean_dec(v_x_127_);
v___x_139_ = 0;
v___x_140_ = l_Lean_SourceInfo_fromRef(v_ref_136_, v___x_139_);
v___x_141_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_142_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__6);
v___x_143_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__9));
lean_inc(v_currMacroScope_135_);
lean_inc(v_quotContext_134_);
v___x_144_ = l_Lean_addMacroScope(v_quotContext_134_, v___x_143_, v_currMacroScope_135_);
v___x_145_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__14));
lean_inc_n(v___x_140_, 2);
v___x_146_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_146_, 0, v___x_140_);
lean_ctor_set(v___x_146_, 1, v___x_142_);
lean_ctor_set(v___x_146_, 2, v___x_144_);
lean_ctor_set(v___x_146_, 3, v___x_145_);
v___x_147_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_148_ = l_Lean_Syntax_node1(v___x_140_, v___x_147_, v___x_138_);
v___x_149_ = l_Lean_Syntax_node2(v___x_140_, v___x_141_, v___x_146_, v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_129_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___boxed(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1(v_x_151_, v_a_152_, v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_154_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__0));
v___x_157_ = l_String_toRawSubstring_x27(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1(lean_object* v_x_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
lean_inc(v_x_185_);
v___x_189_ = l_Lean_Syntax_isOfKind(v_x_185_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_x_185_);
v___x_190_ = lean_box(1);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_a_187_);
return v___x_191_;
}
else
{
lean_object* v_quotContext_192_; lean_object* v_currMacroScope_193_; lean_object* v_ref_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_quotContext_192_ = lean_ctor_get(v_a_186_, 1);
v_currMacroScope_193_ = lean_ctor_get(v_a_186_, 2);
v_ref_194_ = lean_ctor_get(v_a_186_, 5);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = l_Lean_Syntax_getArg(v_x_185_, v___x_195_);
v___x_197_ = lean_unsigned_to_nat(2u);
v___x_198_ = l_Lean_Syntax_getArg(v_x_185_, v___x_197_);
lean_dec(v_x_185_);
v___x_199_ = 0;
v___x_200_ = l_Lean_SourceInfo_fromRef(v_ref_194_, v___x_199_);
v___x_201_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_202_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1);
v___x_203_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3));
lean_inc(v_currMacroScope_193_);
lean_inc(v_quotContext_192_);
v___x_204_ = l_Lean_addMacroScope(v_quotContext_192_, v___x_203_, v_currMacroScope_193_);
v___x_205_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8));
lean_inc_n(v___x_200_, 6);
v___x_206_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_206_, 0, v___x_200_);
lean_ctor_set(v___x_206_, 1, v___x_202_);
lean_ctor_set(v___x_206_, 2, v___x_204_);
lean_ctor_set(v___x_206_, 3, v___x_205_);
v___x_207_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_208_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_209_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_200_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_200_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
lean_inc_ref(v___x_212_);
lean_inc_ref(v___x_210_);
v___x_213_ = l_Lean_Syntax_node3(v___x_200_, v___x_208_, v___x_210_, v___x_196_, v___x_212_);
v___x_214_ = l_Lean_Syntax_node3(v___x_200_, v___x_208_, v___x_210_, v___x_198_, v___x_212_);
v___x_215_ = l_Lean_Syntax_node2(v___x_200_, v___x_207_, v___x_213_, v___x_214_);
v___x_216_ = l_Lean_Syntax_node2(v___x_200_, v___x_201_, v___x_206_, v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_a_187_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___boxed(lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1(v_x_218_, v_a_219_, v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_221_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__14));
v___x_251_ = l_String_toRawSubstring_x27(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__27));
v___x_284_ = l_String_toRawSubstring_x27(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Array_mkArray0(lean_box(0));
return v___x_338_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__68));
v___x_377_ = l_String_toRawSubstring_x27(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__75));
v___x_395_ = l_String_toRawSubstring_x27(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__82));
v___x_413_ = l_String_toRawSubstring_x27(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__91));
v___x_436_ = l_String_toRawSubstring_x27(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__98));
v___x_454_ = l_String_toRawSubstring_x27(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1(lean_object* v_x_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___y_474_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
lean_inc(v_x_470_);
v___x_478_ = l_Lean_Syntax_isOfKind(v_x_470_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v_x_470_);
v___x_479_ = lean_box(1);
v___x_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v_a_472_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = l_Lean_Syntax_getArg(v_x_470_, v___x_482_);
lean_dec(v_x_470_);
v___x_484_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1));
lean_inc(v___x_483_);
v___x_485_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3));
lean_inc(v___x_483_);
v___x_487_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5));
lean_inc(v___x_483_);
v___x_489_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7));
lean_inc(v___x_483_);
v___x_491_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9));
lean_inc(v___x_483_);
v___x_493_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11));
lean_inc(v___x_483_);
v___x_495_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v_x_498_; lean_object* v_xs_499_; lean_object* v_P_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v_x_554_; lean_object* v_ty_555_; lean_object* v_xs_556_; lean_object* v_P_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v_x_616_; lean_object* v_xs_617_; lean_object* v_ty_618_; lean_object* v_ys_619_; lean_object* v_P_620_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___x_684_; 
v___x_496_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13));
lean_inc(v___x_483_);
v___x_684_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_496_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v___x_483_);
v___x_685_ = lean_box(1);
v___x_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v_a_472_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
lean_inc(v___x_687_);
v___x_688_ = l_Lean_Syntax_matchesNull(v___x_687_, v___x_482_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = l_Lean_Syntax_getNumArgs(v___x_687_);
v___x_690_ = lean_nat_dec_le(v___x_482_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_x_691_ = l_Lean_Syntax_getArg(v___x_687_, v___x_481_);
v___x_692_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_691_);
v___x_693_ = l_Lean_Syntax_isOfKind(v_x_691_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_691_);
v___x_695_ = l_Lean_Syntax_isOfKind(v_x_691_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = l_Lean_Syntax_getArg(v_x_691_, v___x_482_);
lean_inc(v___x_696_);
v___x_697_ = l_Lean_Syntax_matchesNull(v___x_696_, v___x_482_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = l_Lean_Syntax_getNumArgs(v___x_696_);
v___x_699_ = lean_nat_dec_le(v___x_482_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec(v___x_698_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_700_; uint8_t v___x_701_; 
v_x_700_ = l_Lean_Syntax_getArg(v___x_696_, v___x_481_);
lean_inc(v_x_700_);
v___x_701_ = l_Lean_Syntax_isOfKind(v_x_700_, v___x_692_);
if (v___x_701_ == 0)
{
lean_dec(v_x_700_);
lean_dec(v___x_698_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_unsigned_to_nat(2u);
v___x_703_ = l_Lean_Syntax_getArg(v_x_691_, v___x_702_);
lean_inc(v___x_703_);
v___x_704_ = l_Lean_Syntax_matchesNull(v___x_703_, v___x_702_);
if (v___x_704_ == 0)
{
lean_dec(v___x_703_);
lean_dec(v_x_700_);
lean_dec(v___x_698_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_unsigned_to_nat(3u);
v___x_706_ = l_Lean_Syntax_getArg(v_x_691_, v___x_705_);
lean_dec(v_x_691_);
v___x_707_ = l_Lean_Syntax_matchesNull(v___x_706_, v___x_481_);
if (v___x_707_ == 0)
{
lean_dec(v___x_703_);
lean_dec(v_x_700_);
lean_dec(v___x_698_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = l_Lean_Syntax_getArg(v___x_483_, v___x_702_);
v___x_709_ = l_Lean_Syntax_matchesNull(v___x_708_, v___x_481_);
if (v___x_709_ == 0)
{
lean_dec(v___x_703_);
lean_dec(v_x_700_);
lean_dec(v___x_698_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_ty_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_P_720_; lean_object* v_ys_721_; lean_object* v_xs_722_; 
v___x_710_ = l_Lean_Syntax_getArgs(v___x_696_);
lean_dec(v___x_696_);
v___x_711_ = l_Array_extract___redArg(v___x_710_, v___x_482_, v___x_698_);
lean_dec_ref(v___x_710_);
v_ty_712_ = l_Lean_Syntax_getArg(v___x_703_, v___x_482_);
lean_dec(v___x_703_);
v___x_713_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_714_ = lean_box(2);
v___x_715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_711_);
v___x_716_ = lean_unsigned_to_nat(4u);
v___x_717_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_718_ = l_Array_extract___redArg(v___x_717_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_717_);
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v___x_714_);
lean_ctor_set(v___x_719_, 1, v___x_713_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
v_P_720_ = l_Lean_Syntax_getArg(v___x_483_, v___x_716_);
lean_dec(v___x_483_);
v_ys_721_ = l_Lean_Syntax_getArgs(v___x_719_);
lean_dec_ref(v___x_719_);
v_xs_722_ = l_Lean_Syntax_getArgs(v___x_715_);
lean_dec_ref(v___x_715_);
v_x_616_ = v_x_700_;
v_xs_617_ = v_xs_722_;
v_ty_618_ = v_ty_712_;
v_ys_619_ = v_ys_721_;
v_P_620_ = v_P_720_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_x_723_; uint8_t v___x_724_; 
v_x_723_ = l_Lean_Syntax_getArg(v___x_696_, v___x_481_);
lean_inc(v_x_723_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_x_723_, v___x_692_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = l_Lean_Syntax_getNumArgs(v___x_696_);
v___x_726_ = lean_nat_dec_le(v___x_482_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_724_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = l_Lean_Syntax_getArg(v_x_691_, v___x_727_);
lean_inc(v___x_728_);
v___x_729_ = l_Lean_Syntax_matchesNull(v___x_728_, v___x_727_);
if (v___x_729_ == 0)
{
lean_dec(v___x_728_);
lean_dec(v___x_725_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = lean_unsigned_to_nat(3u);
v___x_731_ = l_Lean_Syntax_getArg(v_x_691_, v___x_730_);
lean_dec(v_x_691_);
v___x_732_ = l_Lean_Syntax_matchesNull(v___x_731_, v___x_481_);
if (v___x_732_ == 0)
{
lean_dec(v___x_728_);
lean_dec(v___x_725_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = l_Lean_Syntax_getArg(v___x_483_, v___x_727_);
v___x_734_ = l_Lean_Syntax_matchesNull(v___x_733_, v___x_481_);
if (v___x_734_ == 0)
{
lean_dec(v___x_728_);
lean_dec(v___x_725_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_P_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_ty_745_; lean_object* v_ys_746_; lean_object* v_xs_747_; 
v___x_735_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_736_ = l_Array_extract___redArg(v___x_735_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_735_);
v___x_737_ = lean_unsigned_to_nat(4u);
v___x_738_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_739_ = lean_box(2);
v___x_740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
lean_ctor_set(v___x_740_, 2, v___x_736_);
v_P_741_ = l_Lean_Syntax_getArg(v___x_483_, v___x_737_);
lean_dec(v___x_483_);
v___x_742_ = l_Lean_Syntax_getArgs(v___x_696_);
lean_dec(v___x_696_);
v___x_743_ = l_Array_extract___redArg(v___x_742_, v___x_482_, v___x_725_);
lean_dec_ref(v___x_742_);
v___x_744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_744_, 0, v___x_739_);
lean_ctor_set(v___x_744_, 1, v___x_738_);
lean_ctor_set(v___x_744_, 2, v___x_743_);
v_ty_745_ = l_Lean_Syntax_getArg(v___x_728_, v___x_482_);
lean_dec(v___x_728_);
v_ys_746_ = l_Lean_Syntax_getArgs(v___x_740_);
lean_dec_ref(v___x_740_);
v_xs_747_ = l_Lean_Syntax_getArgs(v___x_744_);
lean_dec_ref(v___x_744_);
v_x_616_ = v_x_723_;
v_xs_617_ = v_xs_747_;
v_ty_618_ = v_ty_745_;
v_ys_619_ = v_ys_746_;
v_P_620_ = v_P_741_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(2u);
v___x_749_ = l_Lean_Syntax_getArg(v_x_691_, v___x_748_);
lean_inc(v___x_749_);
v___x_750_ = l_Lean_Syntax_matchesNull(v___x_749_, v___x_748_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = l_Lean_Syntax_getNumArgs(v___x_696_);
v___x_752_ = lean_nat_dec_le(v___x_482_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_724_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_750_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(3u);
v___x_754_ = l_Lean_Syntax_getArg(v_x_691_, v___x_753_);
lean_dec(v_x_691_);
v___x_755_ = l_Lean_Syntax_matchesNull(v___x_754_, v___x_481_);
if (v___x_755_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = l_Lean_Syntax_getArg(v___x_483_, v___x_748_);
v___x_757_ = l_Lean_Syntax_matchesNull(v___x_756_, v___x_481_);
if (v___x_757_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_P_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_ty_768_; lean_object* v_ys_769_; lean_object* v_xs_770_; 
v___x_758_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_759_ = l_Array_extract___redArg(v___x_758_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_758_);
v___x_760_ = lean_unsigned_to_nat(4u);
v___x_761_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_762_ = lean_box(2);
v___x_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
lean_ctor_set(v___x_763_, 2, v___x_759_);
v_P_764_ = l_Lean_Syntax_getArg(v___x_483_, v___x_760_);
lean_dec(v___x_483_);
v___x_765_ = l_Lean_Syntax_getArgs(v___x_696_);
lean_dec(v___x_696_);
v___x_766_ = l_Array_extract___redArg(v___x_765_, v___x_482_, v___x_751_);
lean_dec_ref(v___x_765_);
v___x_767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_767_, 0, v___x_762_);
lean_ctor_set(v___x_767_, 1, v___x_761_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
v_ty_768_ = l_Lean_Syntax_getArg(v___x_749_, v___x_482_);
lean_dec(v___x_749_);
v_ys_769_ = l_Lean_Syntax_getArgs(v___x_763_);
lean_dec_ref(v___x_763_);
v_xs_770_ = l_Lean_Syntax_getArgs(v___x_767_);
lean_dec_ref(v___x_767_);
v_x_616_ = v_x_723_;
v_xs_617_ = v_xs_770_;
v_ty_618_ = v_ty_768_;
v_ys_619_ = v_ys_769_;
v_P_620_ = v_P_764_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_unsigned_to_nat(3u);
v___x_772_ = l_Lean_Syntax_getArg(v_x_691_, v___x_771_);
lean_dec(v_x_691_);
v___x_773_ = l_Lean_Syntax_matchesNull(v___x_772_, v___x_481_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = l_Lean_Syntax_getNumArgs(v___x_696_);
v___x_775_ = lean_nat_dec_le(v___x_482_, v___x_774_);
if (v___x_775_ == 0)
{
lean_dec(v___x_774_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_724_ == 0)
{
lean_dec(v___x_774_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_750_ == 0)
{
lean_dec(v___x_774_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_773_ == 0)
{
lean_dec(v___x_774_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = l_Lean_Syntax_getArg(v___x_483_, v___x_748_);
v___x_777_ = l_Lean_Syntax_matchesNull(v___x_776_, v___x_481_);
if (v___x_777_ == 0)
{
lean_dec(v___x_774_);
lean_dec(v___x_749_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_P_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v_ty_788_; lean_object* v_ys_789_; lean_object* v_xs_790_; 
v___x_778_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_779_ = l_Array_extract___redArg(v___x_778_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_778_);
v___x_780_ = lean_unsigned_to_nat(4u);
v___x_781_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_782_ = lean_box(2);
v___x_783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
lean_ctor_set(v___x_783_, 2, v___x_779_);
v_P_784_ = l_Lean_Syntax_getArg(v___x_483_, v___x_780_);
lean_dec(v___x_483_);
v___x_785_ = l_Lean_Syntax_getArgs(v___x_696_);
lean_dec(v___x_696_);
v___x_786_ = l_Array_extract___redArg(v___x_785_, v___x_482_, v___x_774_);
lean_dec_ref(v___x_785_);
v___x_787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_787_, 0, v___x_782_);
lean_ctor_set(v___x_787_, 1, v___x_781_);
lean_ctor_set(v___x_787_, 2, v___x_786_);
v_ty_788_ = l_Lean_Syntax_getArg(v___x_749_, v___x_482_);
lean_dec(v___x_749_);
v_ys_789_ = l_Lean_Syntax_getArgs(v___x_783_);
lean_dec_ref(v___x_783_);
v_xs_790_ = l_Lean_Syntax_getArgs(v___x_787_);
lean_dec_ref(v___x_787_);
v_x_616_ = v_x_723_;
v_xs_617_ = v_xs_790_;
v_ty_618_ = v_ty_788_;
v_ys_619_ = v_ys_789_;
v_P_620_ = v_P_784_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_ty_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_ty_791_ = l_Lean_Syntax_getArg(v___x_749_, v___x_482_);
lean_dec(v___x_749_);
v___x_792_ = lean_unsigned_to_nat(4u);
v___x_793_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_794_ = l_Array_extract___redArg(v___x_793_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_793_);
v___x_795_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_796_ = lean_box(2);
v___x_797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_795_);
lean_ctor_set(v___x_797_, 2, v___x_794_);
v___x_798_ = l_Lean_Syntax_getArg(v___x_483_, v___x_748_);
v___x_799_ = l_Lean_Syntax_matchesNull(v___x_798_, v___x_481_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = l_Lean_Syntax_getNumArgs(v___x_696_);
v___x_801_ = lean_nat_dec_le(v___x_482_, v___x_800_);
if (v___x_801_ == 0)
{
lean_dec(v___x_800_);
lean_dec_ref(v___x_797_);
lean_dec(v_ty_791_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_724_ == 0)
{
lean_dec(v___x_800_);
lean_dec_ref(v___x_797_);
lean_dec(v_ty_791_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_750_ == 0)
{
lean_dec(v___x_800_);
lean_dec_ref(v___x_797_);
lean_dec(v_ty_791_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_773_ == 0)
{
lean_dec(v___x_800_);
lean_dec_ref(v___x_797_);
lean_dec(v_ty_791_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_799_ == 0)
{
lean_dec(v___x_800_);
lean_dec_ref(v___x_797_);
lean_dec(v_ty_791_);
lean_dec(v_x_723_);
lean_dec(v___x_696_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_P_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_ys_806_; lean_object* v_xs_807_; 
v_P_802_ = l_Lean_Syntax_getArg(v___x_483_, v___x_792_);
lean_dec(v___x_483_);
v___x_803_ = l_Lean_Syntax_getArgs(v___x_696_);
lean_dec(v___x_696_);
v___x_804_ = l_Array_extract___redArg(v___x_803_, v___x_482_, v___x_800_);
lean_dec_ref(v___x_803_);
v___x_805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_805_, 0, v___x_796_);
lean_ctor_set(v___x_805_, 1, v___x_795_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
v_ys_806_ = l_Lean_Syntax_getArgs(v___x_797_);
lean_dec_ref(v___x_797_);
v_xs_807_ = l_Lean_Syntax_getArgs(v___x_805_);
lean_dec_ref(v___x_805_);
v_x_616_ = v_x_723_;
v_xs_617_ = v_xs_807_;
v_ty_618_ = v_ty_791_;
v_ys_619_ = v_ys_806_;
v_P_620_ = v_P_802_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_P_808_; lean_object* v_xs_809_; 
lean_dec(v___x_696_);
v_P_808_ = l_Lean_Syntax_getArg(v___x_483_, v___x_792_);
lean_dec(v___x_483_);
v_xs_809_ = l_Lean_Syntax_getArgs(v___x_797_);
lean_dec_ref(v___x_797_);
v_x_554_ = v_x_723_;
v_ty_555_ = v_ty_791_;
v_xs_556_ = v_xs_809_;
v_P_557_ = v_P_808_;
v___y_558_ = v_a_471_;
v___y_559_ = v_a_472_;
goto v___jp_553_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_unsigned_to_nat(2u);
v___x_811_ = l_Lean_Syntax_getArg(v___x_483_, v___x_810_);
v___x_812_ = l_Lean_Syntax_matchesNull(v___x_811_, v___x_481_);
if (v___x_812_ == 0)
{
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_P_819_; lean_object* v_xs_820_; 
v___x_813_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_814_ = l_Array_extract___redArg(v___x_813_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_813_);
v___x_815_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_816_ = lean_box(2);
v___x_817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
lean_ctor_set(v___x_817_, 2, v___x_814_);
v___x_818_ = lean_unsigned_to_nat(4u);
v_P_819_ = l_Lean_Syntax_getArg(v___x_483_, v___x_818_);
lean_dec(v___x_483_);
v_xs_820_ = l_Lean_Syntax_getArgs(v___x_817_);
lean_dec_ref(v___x_817_);
v_x_498_ = v_x_691_;
v_xs_499_ = v_xs_820_;
v_P_500_ = v_P_819_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v_x_821_; lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v_x_825_; lean_object* v_ty_826_; lean_object* v_P_827_; lean_object* v___y_828_; lean_object* v___y_829_; 
v_x_821_ = l_Lean_Syntax_getArg(v___x_687_, v___x_481_);
v___x_822_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62));
lean_inc(v_x_821_);
v___x_823_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_876_; lean_object* v_x_878_; lean_object* v_xs_879_; lean_object* v_ty_880_; lean_object* v_P_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v_____discr_943_; lean_object* v_____discr_944_; lean_object* v___y_945_; lean_object* v___y_946_; uint8_t v___x_1057_; 
v___x_876_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_821_);
v___x_1057_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_876_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_821_);
v___x_1059_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = l_Lean_Syntax_getNumArgs(v___x_687_);
v___x_1061_ = lean_nat_dec_le(v___x_482_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_P_1065_; 
v___x_1062_ = lean_unsigned_to_nat(2u);
v___x_1063_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1062_);
v___x_1064_ = lean_unsigned_to_nat(4u);
v_P_1065_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1064_);
lean_dec(v___x_483_);
if (v___x_1059_ == 0)
{
if (v___x_1057_ == 0)
{
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_unsigned_to_nat(3u);
v___x_1067_ = l_Lean_Syntax_getArg(v_x_821_, v___x_482_);
lean_inc(v___x_1067_);
v___x_1068_ = l_Lean_Syntax_matchesNull(v___x_1067_, v___x_482_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = l_Lean_Syntax_getNumArgs(v___x_1067_);
v___x_1070_ = lean_nat_dec_le(v___x_482_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v___x_1069_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1071_; uint8_t v___x_1072_; 
v_x_1071_ = l_Lean_Syntax_getArg(v___x_1067_, v___x_481_);
lean_inc(v_x_1071_);
v___x_1072_ = l_Lean_Syntax_isOfKind(v_x_1071_, v___x_1058_);
if (v___x_1072_ == 0)
{
lean_dec(v_x_1071_);
lean_dec(v___x_1069_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1062_);
lean_inc(v___x_1073_);
v___x_1074_ = l_Lean_Syntax_matchesNull(v___x_1073_, v___x_1062_);
if (v___x_1074_ == 0)
{
lean_dec(v___x_1073_);
lean_dec(v_x_1071_);
lean_dec(v___x_1069_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1066_);
lean_dec(v_x_821_);
v___x_1076_ = l_Lean_Syntax_matchesNull(v___x_1075_, v___x_481_);
if (v___x_1076_ == 0)
{
lean_dec(v___x_1073_);
lean_dec(v_x_1071_);
lean_dec(v___x_1069_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1077_; 
v___x_1077_ = l_Lean_Syntax_matchesNull(v___x_1063_, v___x_481_);
if (v___x_1077_ == 0)
{
lean_dec(v___x_1073_);
lean_dec(v_x_1071_);
lean_dec(v___x_1069_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_ty_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_ys_1087_; lean_object* v_xs_1088_; 
v___x_1078_ = l_Lean_Syntax_getArgs(v___x_1067_);
lean_dec(v___x_1067_);
v___x_1079_ = l_Array_extract___redArg(v___x_1078_, v___x_482_, v___x_1069_);
lean_dec_ref(v___x_1078_);
v_ty_1080_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_482_);
lean_dec(v___x_1073_);
v___x_1081_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1082_ = lean_box(2);
v___x_1083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set(v___x_1083_, 2, v___x_1079_);
v___x_1084_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1085_ = l_Array_extract___redArg(v___x_1084_, v___x_482_, v___x_1060_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1082_);
lean_ctor_set(v___x_1086_, 1, v___x_1081_);
lean_ctor_set(v___x_1086_, 2, v___x_1085_);
v_ys_1087_ = l_Lean_Syntax_getArgs(v___x_1086_);
lean_dec_ref(v___x_1086_);
v_xs_1088_ = l_Lean_Syntax_getArgs(v___x_1083_);
lean_dec_ref(v___x_1083_);
v_x_616_ = v_x_1071_;
v_xs_617_ = v_xs_1088_;
v_ty_618_ = v_ty_1080_;
v_ys_619_ = v_ys_1087_;
v_P_620_ = v_P_1065_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_x_1089_; uint8_t v___x_1090_; 
v_x_1089_ = l_Lean_Syntax_getArg(v___x_1067_, v___x_481_);
lean_inc(v_x_1089_);
v___x_1090_ = l_Lean_Syntax_isOfKind(v_x_1089_, v___x_1058_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = l_Lean_Syntax_getNumArgs(v___x_1067_);
v___x_1092_ = lean_nat_dec_le(v___x_482_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_dec(v___x_1091_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1090_ == 0)
{
lean_dec(v___x_1091_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1062_);
lean_inc(v___x_1093_);
v___x_1094_ = l_Lean_Syntax_matchesNull(v___x_1093_, v___x_1062_);
if (v___x_1094_ == 0)
{
lean_dec(v___x_1093_);
lean_dec(v___x_1091_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1066_);
lean_dec(v_x_821_);
v___x_1096_ = l_Lean_Syntax_matchesNull(v___x_1095_, v___x_481_);
if (v___x_1096_ == 0)
{
lean_dec(v___x_1093_);
lean_dec(v___x_1091_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_Syntax_matchesNull(v___x_1063_, v___x_481_);
if (v___x_1097_ == 0)
{
lean_dec(v___x_1093_);
lean_dec(v___x_1091_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_ty_1106_; lean_object* v_ys_1107_; lean_object* v_xs_1108_; 
v___x_1098_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1099_ = l_Array_extract___redArg(v___x_1098_, v___x_482_, v___x_1060_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1101_ = lean_box(2);
v___x_1102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1100_);
lean_ctor_set(v___x_1102_, 2, v___x_1099_);
v___x_1103_ = l_Lean_Syntax_getArgs(v___x_1067_);
lean_dec(v___x_1067_);
v___x_1104_ = l_Array_extract___redArg(v___x_1103_, v___x_482_, v___x_1091_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1101_);
lean_ctor_set(v___x_1105_, 1, v___x_1100_);
lean_ctor_set(v___x_1105_, 2, v___x_1104_);
v_ty_1106_ = l_Lean_Syntax_getArg(v___x_1093_, v___x_482_);
lean_dec(v___x_1093_);
v_ys_1107_ = l_Lean_Syntax_getArgs(v___x_1102_);
lean_dec_ref(v___x_1102_);
v_xs_1108_ = l_Lean_Syntax_getArgs(v___x_1105_);
lean_dec_ref(v___x_1105_);
v_x_616_ = v_x_1089_;
v_xs_617_ = v_xs_1108_;
v_ty_618_ = v_ty_1106_;
v_ys_619_ = v_ys_1107_;
v_P_620_ = v_P_1065_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1062_);
lean_inc(v___x_1109_);
v___x_1110_ = l_Lean_Syntax_matchesNull(v___x_1109_, v___x_1062_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = l_Lean_Syntax_getNumArgs(v___x_1067_);
v___x_1112_ = lean_nat_dec_le(v___x_482_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_dec(v___x_1111_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1090_ == 0)
{
lean_dec(v___x_1111_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1110_ == 0)
{
lean_dec(v___x_1111_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1066_);
lean_dec(v_x_821_);
v___x_1114_ = l_Lean_Syntax_matchesNull(v___x_1113_, v___x_481_);
if (v___x_1114_ == 0)
{
lean_dec(v___x_1111_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_Syntax_matchesNull(v___x_1063_, v___x_481_);
if (v___x_1115_ == 0)
{
lean_dec(v___x_1111_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_ty_1124_; lean_object* v_ys_1125_; lean_object* v_xs_1126_; 
v___x_1116_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1117_ = l_Array_extract___redArg(v___x_1116_, v___x_482_, v___x_1060_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1119_ = lean_box(2);
v___x_1120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
lean_ctor_set(v___x_1120_, 2, v___x_1117_);
v___x_1121_ = l_Lean_Syntax_getArgs(v___x_1067_);
lean_dec(v___x_1067_);
v___x_1122_ = l_Array_extract___redArg(v___x_1121_, v___x_482_, v___x_1111_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1119_);
lean_ctor_set(v___x_1123_, 1, v___x_1118_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
v_ty_1124_ = l_Lean_Syntax_getArg(v___x_1109_, v___x_482_);
lean_dec(v___x_1109_);
v_ys_1125_ = l_Lean_Syntax_getArgs(v___x_1120_);
lean_dec_ref(v___x_1120_);
v_xs_1126_ = l_Lean_Syntax_getArgs(v___x_1123_);
lean_dec_ref(v___x_1123_);
v_x_616_ = v_x_1089_;
v_xs_617_ = v_xs_1126_;
v_ty_618_ = v_ty_1124_;
v_ys_619_ = v_ys_1125_;
v_P_620_ = v_P_1065_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1066_);
lean_dec(v_x_821_);
v___x_1128_ = l_Lean_Syntax_matchesNull(v___x_1127_, v___x_481_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = l_Lean_Syntax_getNumArgs(v___x_1067_);
v___x_1130_ = lean_nat_dec_le(v___x_482_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_dec(v___x_1129_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1090_ == 0)
{
lean_dec(v___x_1129_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1110_ == 0)
{
lean_dec(v___x_1129_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1128_ == 0)
{
lean_dec(v___x_1129_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1063_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_Syntax_matchesNull(v___x_1063_, v___x_481_);
if (v___x_1131_ == 0)
{
lean_dec(v___x_1129_);
lean_dec(v___x_1109_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
lean_dec(v___x_1060_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_ty_1140_; lean_object* v_ys_1141_; lean_object* v_xs_1142_; 
v___x_1132_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1133_ = l_Array_extract___redArg(v___x_1132_, v___x_482_, v___x_1060_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1135_ = lean_box(2);
v___x_1136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
lean_ctor_set(v___x_1136_, 2, v___x_1133_);
v___x_1137_ = l_Lean_Syntax_getArgs(v___x_1067_);
lean_dec(v___x_1067_);
v___x_1138_ = l_Array_extract___redArg(v___x_1137_, v___x_482_, v___x_1129_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1135_);
lean_ctor_set(v___x_1139_, 1, v___x_1134_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
v_ty_1140_ = l_Lean_Syntax_getArg(v___x_1109_, v___x_482_);
lean_dec(v___x_1109_);
v_ys_1141_ = l_Lean_Syntax_getArgs(v___x_1136_);
lean_dec_ref(v___x_1136_);
v_xs_1142_ = l_Lean_Syntax_getArgs(v___x_1139_);
lean_dec_ref(v___x_1139_);
v_x_616_ = v_x_1089_;
v_xs_617_ = v_xs_1142_;
v_ty_618_ = v_ty_1140_;
v_ys_619_ = v_ys_1141_;
v_P_620_ = v_P_1065_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_ty_1143_ = l_Lean_Syntax_getArg(v___x_1109_, v___x_482_);
lean_dec(v___x_1109_);
v___x_1144_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1145_ = l_Array_extract___redArg(v___x_1144_, v___x_482_, v___x_1060_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1147_ = lean_box(2);
v___x_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___x_1146_);
lean_ctor_set(v___x_1148_, 2, v___x_1145_);
v___x_1149_ = l_Lean_Syntax_matchesNull(v___x_1063_, v___x_481_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = l_Lean_Syntax_getNumArgs(v___x_1067_);
v___x_1151_ = lean_nat_dec_le(v___x_482_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_dec(v___x_1150_);
lean_dec_ref(v___x_1148_);
lean_dec(v_ty_1143_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1090_ == 0)
{
lean_dec(v___x_1150_);
lean_dec_ref(v___x_1148_);
lean_dec(v_ty_1143_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1110_ == 0)
{
lean_dec(v___x_1150_);
lean_dec_ref(v___x_1148_);
lean_dec(v_ty_1143_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1128_ == 0)
{
lean_dec(v___x_1150_);
lean_dec_ref(v___x_1148_);
lean_dec(v_ty_1143_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1149_ == 0)
{
lean_dec(v___x_1150_);
lean_dec_ref(v___x_1148_);
lean_dec(v_ty_1143_);
lean_dec(v_x_1089_);
lean_dec(v___x_1067_);
lean_dec(v_P_1065_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_ys_1155_; lean_object* v_xs_1156_; 
v___x_1152_ = l_Lean_Syntax_getArgs(v___x_1067_);
lean_dec(v___x_1067_);
v___x_1153_ = l_Array_extract___redArg(v___x_1152_, v___x_482_, v___x_1150_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1147_);
lean_ctor_set(v___x_1154_, 1, v___x_1146_);
lean_ctor_set(v___x_1154_, 2, v___x_1153_);
v_ys_1155_ = l_Lean_Syntax_getArgs(v___x_1148_);
lean_dec_ref(v___x_1148_);
v_xs_1156_ = l_Lean_Syntax_getArgs(v___x_1154_);
lean_dec_ref(v___x_1154_);
v_x_616_ = v_x_1089_;
v_xs_617_ = v_xs_1156_;
v_ty_618_ = v_ty_1143_;
v_ys_619_ = v_ys_1155_;
v_P_620_ = v_P_1065_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1157_; 
lean_dec(v___x_1067_);
v_xs_1157_ = l_Lean_Syntax_getArgs(v___x_1148_);
lean_dec_ref(v___x_1148_);
v_x_554_ = v_x_1089_;
v_ty_555_ = v_ty_1143_;
v_xs_556_ = v_xs_1157_;
v_P_557_ = v_P_1065_;
v___y_558_ = v_a_471_;
v___y_559_ = v_a_472_;
goto v___jp_553_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1158_; 
v___x_1158_ = l_Lean_Syntax_matchesNull(v___x_1063_, v___x_481_);
if (v___x_1158_ == 0)
{
lean_dec(v_P_1065_);
lean_dec(v___x_1060_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_xs_1164_; 
v___x_1159_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1160_ = l_Array_extract___redArg(v___x_1159_, v___x_482_, v___x_1060_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1162_ = lean_box(2);
v___x_1163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1161_);
lean_ctor_set(v___x_1163_, 2, v___x_1160_);
v_xs_1164_ = l_Lean_Syntax_getArgs(v___x_1163_);
lean_dec_ref(v___x_1163_);
v_x_498_ = v_x_821_;
v_xs_499_ = v_xs_1164_;
v_P_500_ = v_P_1065_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_unsigned_to_nat(2u);
v___x_1166_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1165_);
v___x_1167_ = l_Lean_Syntax_matchesNull(v___x_1166_, v___x_481_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = l_Lean_Syntax_getNumArgs(v___x_687_);
v___x_1169_ = lean_nat_dec_le(v___x_482_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1170_; lean_object* v_P_1171_; 
v___x_1170_ = lean_unsigned_to_nat(4u);
v_P_1171_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1170_);
lean_dec(v___x_483_);
if (v___x_1059_ == 0)
{
if (v___x_1057_ == 0)
{
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = lean_unsigned_to_nat(3u);
v___x_1173_ = l_Lean_Syntax_getArg(v_x_821_, v___x_482_);
lean_inc(v___x_1173_);
v___x_1174_ = l_Lean_Syntax_matchesNull(v___x_1173_, v___x_482_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = l_Lean_Syntax_getNumArgs(v___x_1173_);
v___x_1176_ = lean_nat_dec_le(v___x_482_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec(v___x_1175_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1177_; uint8_t v___x_1178_; 
v_x_1177_ = l_Lean_Syntax_getArg(v___x_1173_, v___x_481_);
lean_inc(v_x_1177_);
v___x_1178_ = l_Lean_Syntax_isOfKind(v_x_1177_, v___x_1058_);
if (v___x_1178_ == 0)
{
lean_dec(v_x_1177_);
lean_dec(v___x_1175_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1165_);
lean_inc(v___x_1179_);
v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1179_, v___x_1165_);
if (v___x_1180_ == 0)
{
lean_dec(v___x_1179_);
lean_dec(v_x_1177_);
lean_dec(v___x_1175_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1172_);
lean_dec(v_x_821_);
v___x_1182_ = l_Lean_Syntax_matchesNull(v___x_1181_, v___x_481_);
if (v___x_1182_ == 0)
{
lean_dec(v___x_1179_);
lean_dec(v_x_1177_);
lean_dec(v___x_1175_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1167_ == 0)
{
lean_dec(v___x_1179_);
lean_dec(v_x_1177_);
lean_dec(v___x_1175_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_ty_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_ys_1192_; lean_object* v_xs_1193_; 
v___x_1183_ = l_Lean_Syntax_getArgs(v___x_1173_);
lean_dec(v___x_1173_);
v___x_1184_ = l_Array_extract___redArg(v___x_1183_, v___x_482_, v___x_1175_);
lean_dec_ref(v___x_1183_);
v_ty_1185_ = l_Lean_Syntax_getArg(v___x_1179_, v___x_482_);
lean_dec(v___x_1179_);
v___x_1186_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1187_ = lean_box(2);
v___x_1188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___x_1186_);
lean_ctor_set(v___x_1188_, 2, v___x_1184_);
v___x_1189_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1190_ = l_Array_extract___redArg(v___x_1189_, v___x_482_, v___x_1168_);
lean_dec_ref(v___x_1189_);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1187_);
lean_ctor_set(v___x_1191_, 1, v___x_1186_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
v_ys_1192_ = l_Lean_Syntax_getArgs(v___x_1191_);
lean_dec_ref(v___x_1191_);
v_xs_1193_ = l_Lean_Syntax_getArgs(v___x_1188_);
lean_dec_ref(v___x_1188_);
v_x_616_ = v_x_1177_;
v_xs_617_ = v_xs_1193_;
v_ty_618_ = v_ty_1185_;
v_ys_619_ = v_ys_1192_;
v_P_620_ = v_P_1171_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_x_1194_; uint8_t v___x_1195_; 
v_x_1194_ = l_Lean_Syntax_getArg(v___x_1173_, v___x_481_);
lean_inc(v_x_1194_);
v___x_1195_ = l_Lean_Syntax_isOfKind(v_x_1194_, v___x_1058_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = l_Lean_Syntax_getNumArgs(v___x_1173_);
v___x_1197_ = lean_nat_dec_le(v___x_482_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_dec(v___x_1196_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1195_ == 0)
{
lean_dec(v___x_1196_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1165_);
lean_inc(v___x_1198_);
v___x_1199_ = l_Lean_Syntax_matchesNull(v___x_1198_, v___x_1165_);
if (v___x_1199_ == 0)
{
lean_dec(v___x_1198_);
lean_dec(v___x_1196_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1172_);
lean_dec(v_x_821_);
v___x_1201_ = l_Lean_Syntax_matchesNull(v___x_1200_, v___x_481_);
if (v___x_1201_ == 0)
{
lean_dec(v___x_1198_);
lean_dec(v___x_1196_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1167_ == 0)
{
lean_dec(v___x_1198_);
lean_dec(v___x_1196_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_ty_1210_; lean_object* v_ys_1211_; lean_object* v_xs_1212_; 
v___x_1202_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1203_ = l_Array_extract___redArg(v___x_1202_, v___x_482_, v___x_1168_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1205_ = lean_box(2);
v___x_1206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1204_);
lean_ctor_set(v___x_1206_, 2, v___x_1203_);
v___x_1207_ = l_Lean_Syntax_getArgs(v___x_1173_);
lean_dec(v___x_1173_);
v___x_1208_ = l_Array_extract___redArg(v___x_1207_, v___x_482_, v___x_1196_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1205_);
lean_ctor_set(v___x_1209_, 1, v___x_1204_);
lean_ctor_set(v___x_1209_, 2, v___x_1208_);
v_ty_1210_ = l_Lean_Syntax_getArg(v___x_1198_, v___x_482_);
lean_dec(v___x_1198_);
v_ys_1211_ = l_Lean_Syntax_getArgs(v___x_1206_);
lean_dec_ref(v___x_1206_);
v_xs_1212_ = l_Lean_Syntax_getArgs(v___x_1209_);
lean_dec_ref(v___x_1209_);
v_x_616_ = v_x_1194_;
v_xs_617_ = v_xs_1212_;
v_ty_618_ = v_ty_1210_;
v_ys_619_ = v_ys_1211_;
v_P_620_ = v_P_1171_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1165_);
lean_inc(v___x_1213_);
v___x_1214_ = l_Lean_Syntax_matchesNull(v___x_1213_, v___x_1165_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = l_Lean_Syntax_getNumArgs(v___x_1173_);
v___x_1216_ = lean_nat_dec_le(v___x_482_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec(v___x_1215_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1195_ == 0)
{
lean_dec(v___x_1215_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1214_ == 0)
{
lean_dec(v___x_1215_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1172_);
lean_dec(v_x_821_);
v___x_1218_ = l_Lean_Syntax_matchesNull(v___x_1217_, v___x_481_);
if (v___x_1218_ == 0)
{
lean_dec(v___x_1215_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1167_ == 0)
{
lean_dec(v___x_1215_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_ty_1227_; lean_object* v_ys_1228_; lean_object* v_xs_1229_; 
v___x_1219_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1220_ = l_Array_extract___redArg(v___x_1219_, v___x_482_, v___x_1168_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1222_ = lean_box(2);
v___x_1223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1221_);
lean_ctor_set(v___x_1223_, 2, v___x_1220_);
v___x_1224_ = l_Lean_Syntax_getArgs(v___x_1173_);
lean_dec(v___x_1173_);
v___x_1225_ = l_Array_extract___redArg(v___x_1224_, v___x_482_, v___x_1215_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1222_);
lean_ctor_set(v___x_1226_, 1, v___x_1221_);
lean_ctor_set(v___x_1226_, 2, v___x_1225_);
v_ty_1227_ = l_Lean_Syntax_getArg(v___x_1213_, v___x_482_);
lean_dec(v___x_1213_);
v_ys_1228_ = l_Lean_Syntax_getArgs(v___x_1223_);
lean_dec_ref(v___x_1223_);
v_xs_1229_ = l_Lean_Syntax_getArgs(v___x_1226_);
lean_dec_ref(v___x_1226_);
v_x_616_ = v_x_1194_;
v_xs_617_ = v_xs_1229_;
v_ty_618_ = v_ty_1227_;
v_ys_619_ = v_ys_1228_;
v_P_620_ = v_P_1171_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1172_);
lean_dec(v_x_821_);
v___x_1231_ = l_Lean_Syntax_matchesNull(v___x_1230_, v___x_481_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = l_Lean_Syntax_getNumArgs(v___x_1173_);
v___x_1233_ = lean_nat_dec_le(v___x_482_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1195_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1214_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1231_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1167_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v___x_1213_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_ty_1242_; lean_object* v_ys_1243_; lean_object* v_xs_1244_; 
v___x_1234_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1235_ = l_Array_extract___redArg(v___x_1234_, v___x_482_, v___x_1168_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1237_ = lean_box(2);
v___x_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1236_);
lean_ctor_set(v___x_1238_, 2, v___x_1235_);
v___x_1239_ = l_Lean_Syntax_getArgs(v___x_1173_);
lean_dec(v___x_1173_);
v___x_1240_ = l_Array_extract___redArg(v___x_1239_, v___x_482_, v___x_1232_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1237_);
lean_ctor_set(v___x_1241_, 1, v___x_1236_);
lean_ctor_set(v___x_1241_, 2, v___x_1240_);
v_ty_1242_ = l_Lean_Syntax_getArg(v___x_1213_, v___x_482_);
lean_dec(v___x_1213_);
v_ys_1243_ = l_Lean_Syntax_getArgs(v___x_1238_);
lean_dec_ref(v___x_1238_);
v_xs_1244_ = l_Lean_Syntax_getArgs(v___x_1241_);
lean_dec_ref(v___x_1241_);
v_x_616_ = v_x_1194_;
v_xs_617_ = v_xs_1244_;
v_ty_618_ = v_ty_1242_;
v_ys_619_ = v_ys_1243_;
v_P_620_ = v_P_1171_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_ty_1245_ = l_Lean_Syntax_getArg(v___x_1213_, v___x_482_);
lean_dec(v___x_1213_);
v___x_1246_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1247_ = l_Array_extract___redArg(v___x_1246_, v___x_482_, v___x_1168_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1249_ = lean_box(2);
v___x_1250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1248_);
lean_ctor_set(v___x_1250_, 2, v___x_1247_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = l_Lean_Syntax_getNumArgs(v___x_1173_);
v___x_1252_ = lean_nat_dec_le(v___x_482_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec(v_ty_1245_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1195_ == 0)
{
lean_dec(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec(v_ty_1245_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1214_ == 0)
{
lean_dec(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec(v_ty_1245_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1231_ == 0)
{
lean_dec(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec(v_ty_1245_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1167_ == 0)
{
lean_dec(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec(v_ty_1245_);
lean_dec(v_x_1194_);
lean_dec(v___x_1173_);
lean_dec(v_P_1171_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_ys_1256_; lean_object* v_xs_1257_; 
v___x_1253_ = l_Lean_Syntax_getArgs(v___x_1173_);
lean_dec(v___x_1173_);
v___x_1254_ = l_Array_extract___redArg(v___x_1253_, v___x_482_, v___x_1251_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1249_);
lean_ctor_set(v___x_1255_, 1, v___x_1248_);
lean_ctor_set(v___x_1255_, 2, v___x_1254_);
v_ys_1256_ = l_Lean_Syntax_getArgs(v___x_1250_);
lean_dec_ref(v___x_1250_);
v_xs_1257_ = l_Lean_Syntax_getArgs(v___x_1255_);
lean_dec_ref(v___x_1255_);
v_x_616_ = v_x_1194_;
v_xs_617_ = v_xs_1257_;
v_ty_618_ = v_ty_1245_;
v_ys_619_ = v_ys_1256_;
v_P_620_ = v_P_1171_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1258_; 
lean_dec(v___x_1173_);
v_xs_1258_ = l_Lean_Syntax_getArgs(v___x_1250_);
lean_dec_ref(v___x_1250_);
v_x_554_ = v_x_1194_;
v_ty_555_ = v_ty_1245_;
v_xs_556_ = v_xs_1258_;
v_P_557_ = v_P_1171_;
v___y_558_ = v_a_471_;
v___y_559_ = v_a_472_;
goto v___jp_553_;
}
}
}
}
}
}
}
else
{
if (v___x_1167_ == 0)
{
lean_dec(v_P_1171_);
lean_dec(v___x_1168_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_xs_1264_; 
v___x_1259_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1260_ = l_Array_extract___redArg(v___x_1259_, v___x_482_, v___x_1168_);
lean_dec_ref(v___x_1259_);
v___x_1261_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1262_ = lean_box(2);
v___x_1263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
lean_ctor_set(v___x_1263_, 2, v___x_1260_);
v_xs_1264_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec_ref(v___x_1263_);
v_x_498_ = v_x_821_;
v_xs_499_ = v_xs_1264_;
v_P_500_ = v_P_1171_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v_quotContext_1265_; lean_object* v_currMacroScope_1266_; lean_object* v_ref_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v___x_687_);
v_quotContext_1265_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1266_ = lean_ctor_get(v_a_471_, 2);
v_ref_1267_ = lean_ctor_get(v_a_471_, 5);
v___x_1268_ = lean_unsigned_to_nat(4u);
v___x_1269_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1268_);
lean_dec(v___x_483_);
v___x_1270_ = l_Lean_SourceInfo_fromRef(v_ref_1267_, v___x_1057_);
v___x_1271_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1272_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1273_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1266_, 2);
lean_inc_n(v_quotContext_1265_, 2);
v___x_1274_ = l_Lean_addMacroScope(v_quotContext_1265_, v___x_1273_, v_currMacroScope_1266_);
v___x_1275_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1270_, 16);
v___x_1276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1270_);
lean_ctor_set(v___x_1276_, 1, v___x_1272_);
lean_ctor_set(v___x_1276_, 2, v___x_1274_);
lean_ctor_set(v___x_1276_, 3, v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1278_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1279_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1280_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1270_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1283_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1284_ = lean_box(0);
v___x_1285_ = l_Lean_addMacroScope(v_quotContext_1265_, v___x_1284_, v_currMacroScope_1266_);
v___x_1286_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1287_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1270_);
lean_ctor_set(v___x_1287_, 1, v___x_1283_);
lean_ctor_set(v___x_1287_, 2, v___x_1285_);
lean_ctor_set(v___x_1287_, 3, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node1(v___x_1270_, v___x_1282_, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_node2(v___x_1270_, v___x_1279_, v___x_1281_, v___x_1288_);
v___x_1290_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1291_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1270_);
lean_ctor_set(v___x_1292_, 1, v___x_1290_);
v___x_1293_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1294_ = l_Lean_Syntax_node1(v___x_1270_, v___x_1277_, v_x_821_);
v___x_1295_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1270_);
lean_ctor_set(v___x_1296_, 1, v___x_1277_);
lean_ctor_set(v___x_1296_, 2, v___x_1295_);
v___x_1297_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1270_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1270_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1270_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_inc_ref(v___x_1302_);
v___x_1303_ = l_Lean_Syntax_node3(v___x_1270_, v___x_477_, v___x_1300_, v___x_1269_, v___x_1302_);
v___x_1304_ = l_Lean_Syntax_node4(v___x_1270_, v___x_1293_, v___x_1294_, v___x_1296_, v___x_1298_, v___x_1303_);
v___x_1305_ = l_Lean_Syntax_node2(v___x_1270_, v___x_1291_, v___x_1292_, v___x_1304_);
v___x_1306_ = l_Lean_Syntax_node3(v___x_1270_, v___x_1278_, v___x_1289_, v___x_1305_, v___x_1302_);
v___x_1307_ = l_Lean_Syntax_node1(v___x_1270_, v___x_1277_, v___x_1306_);
v___x_1308_ = l_Lean_Syntax_node2(v___x_1270_, v___x_1271_, v___x_1276_, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_a_472_);
return v___x_1309_;
}
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1310_ = l_Lean_Syntax_getArg(v_x_821_, v___x_482_);
v___x_1311_ = l_Lean_Syntax_getNumArgs(v___x_1310_);
v___x_1312_ = lean_nat_dec_le(v___x_482_, v___x_1311_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
lean_inc(v___x_1310_);
v___x_1313_ = l_Lean_Syntax_matchesNull(v___x_1310_, v___x_482_);
if (v___x_1313_ == 0)
{
if (v___x_1312_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v___x_1314_ = lean_unsigned_to_nat(2u);
v___x_1315_ = lean_unsigned_to_nat(4u);
v___x_1316_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1314_);
v___x_1317_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1315_);
lean_dec(v___x_483_);
v_____discr_943_ = v___x_1316_;
v_____discr_944_ = v___x_1317_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v_x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v_x_1318_ = l_Lean_Syntax_getArg(v___x_1310_, v___x_481_);
v___x_1319_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1318_);
v___x_1320_ = l_Lean_Syntax_isOfKind(v_x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_x_1318_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v___x_1321_ = lean_unsigned_to_nat(2u);
v___x_1322_ = lean_unsigned_to_nat(4u);
v___x_1323_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1321_);
v___x_1324_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1322_);
lean_dec(v___x_483_);
v_____discr_943_ = v___x_1323_;
v_____discr_944_ = v___x_1324_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1325_ = lean_unsigned_to_nat(2u);
v___x_1326_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1325_);
lean_inc(v___x_1326_);
v___x_1327_ = l_Lean_Syntax_matchesNull(v___x_1326_, v___x_1325_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec(v___x_1326_);
lean_dec(v_x_1318_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v___x_1328_ = lean_unsigned_to_nat(4u);
v___x_1329_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1325_);
v___x_1330_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1328_);
lean_dec(v___x_483_);
v_____discr_943_ = v___x_1329_;
v_____discr_944_ = v___x_1330_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = lean_unsigned_to_nat(3u);
v___x_1332_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1331_);
v___x_1333_ = l_Lean_Syntax_matchesNull(v___x_1332_, v___x_481_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v___x_1326_);
lean_dec(v_x_1318_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v___x_1334_ = lean_unsigned_to_nat(4u);
v___x_1335_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1325_);
v___x_1336_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1334_);
lean_dec(v___x_483_);
v_____discr_943_ = v___x_1335_;
v_____discr_944_ = v___x_1336_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = lean_unsigned_to_nat(4u);
v___x_1338_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1325_);
lean_inc(v___x_1338_);
v___x_1339_ = l_Lean_Syntax_matchesNull(v___x_1338_, v___x_481_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec(v___x_1326_);
lean_dec(v_x_1318_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v___x_1340_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1337_);
lean_dec(v___x_483_);
v_____discr_943_ = v___x_1338_;
v_____discr_944_ = v___x_1340_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_ty_1346_; lean_object* v_P_1347_; lean_object* v_xs_1348_; 
lean_dec(v___x_1338_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1341_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1342_ = l_Array_extract___redArg(v___x_1341_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1344_ = lean_box(2);
v___x_1345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
lean_ctor_set(v___x_1345_, 2, v___x_1342_);
v_ty_1346_ = l_Lean_Syntax_getArg(v___x_1326_, v___x_482_);
lean_dec(v___x_1326_);
v_P_1347_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1337_);
lean_dec(v___x_483_);
v_xs_1348_ = l_Lean_Syntax_getArgs(v___x_1345_);
lean_dec_ref(v___x_1345_);
v_x_878_ = v_x_1318_;
v_xs_879_ = v_xs_1348_;
v_ty_880_ = v_ty_1346_;
v_P_881_ = v_P_1347_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v_x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_x_1349_ = l_Lean_Syntax_getArg(v___x_1310_, v___x_481_);
v___x_1350_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1349_);
v___x_1351_ = l_Lean_Syntax_isOfKind(v_x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_P_1355_; 
v___x_1352_ = lean_unsigned_to_nat(2u);
v___x_1353_ = lean_unsigned_to_nat(4u);
v___x_1354_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1352_);
v_P_1355_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1353_);
lean_dec(v___x_483_);
if (v___x_1312_ == 0)
{
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1354_;
v_____discr_944_ = v_P_1355_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1351_ == 0)
{
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1354_;
v_____discr_944_ = v_P_1355_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1352_);
lean_inc(v___x_1356_);
v___x_1357_ = l_Lean_Syntax_matchesNull(v___x_1356_, v___x_1352_);
if (v___x_1357_ == 0)
{
lean_dec(v___x_1356_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1354_;
v_____discr_944_ = v_P_1355_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = lean_unsigned_to_nat(3u);
v___x_1359_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1358_);
v___x_1360_ = l_Lean_Syntax_matchesNull(v___x_1359_, v___x_481_);
if (v___x_1360_ == 0)
{
lean_dec(v___x_1356_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1354_;
v_____discr_944_ = v_P_1355_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1361_; 
lean_inc(v___x_1354_);
v___x_1361_ = l_Lean_Syntax_matchesNull(v___x_1354_, v___x_481_);
if (v___x_1361_ == 0)
{
lean_dec(v___x_1356_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1354_;
v_____discr_944_ = v_P_1355_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_ty_1367_; lean_object* v_xs_1368_; 
lean_dec(v___x_1354_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1362_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1363_ = l_Array_extract___redArg(v___x_1362_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1365_ = lean_box(2);
v___x_1366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1364_);
lean_ctor_set(v___x_1366_, 2, v___x_1363_);
v_ty_1367_ = l_Lean_Syntax_getArg(v___x_1356_, v___x_482_);
lean_dec(v___x_1356_);
v_xs_1368_ = l_Lean_Syntax_getArgs(v___x_1366_);
lean_dec_ref(v___x_1366_);
v_x_878_ = v_x_1349_;
v_xs_879_ = v_xs_1368_;
v_ty_880_ = v_ty_1367_;
v_P_881_ = v_P_1355_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_unsigned_to_nat(2u);
v___x_1370_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1369_);
lean_inc(v___x_1370_);
v___x_1371_ = l_Lean_Syntax_matchesNull(v___x_1370_, v___x_1369_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_P_1374_; 
v___x_1372_ = lean_unsigned_to_nat(4u);
v___x_1373_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1369_);
v_P_1374_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1372_);
lean_dec(v___x_483_);
if (v___x_1312_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1373_;
v_____discr_944_ = v_P_1374_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1351_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1373_;
v_____discr_944_ = v_P_1374_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1371_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1373_;
v_____discr_944_ = v_P_1374_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(3u);
v___x_1376_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1375_);
v___x_1377_ = l_Lean_Syntax_matchesNull(v___x_1376_, v___x_481_);
if (v___x_1377_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1373_;
v_____discr_944_ = v_P_1374_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1378_; 
lean_inc(v___x_1373_);
v___x_1378_ = l_Lean_Syntax_matchesNull(v___x_1373_, v___x_481_);
if (v___x_1378_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1373_;
v_____discr_944_ = v_P_1374_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_ty_1384_; lean_object* v_xs_1385_; 
lean_dec(v___x_1373_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1379_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1380_ = l_Array_extract___redArg(v___x_1379_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1382_ = lean_box(2);
v___x_1383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1381_);
lean_ctor_set(v___x_1383_, 2, v___x_1380_);
v_ty_1384_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_482_);
lean_dec(v___x_1370_);
v_xs_1385_ = l_Lean_Syntax_getArgs(v___x_1383_);
lean_dec_ref(v___x_1383_);
v_x_878_ = v_x_1349_;
v_xs_879_ = v_xs_1385_;
v_ty_880_ = v_ty_1384_;
v_P_881_ = v_P_1374_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = lean_unsigned_to_nat(3u);
v___x_1387_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1386_);
v___x_1388_ = l_Lean_Syntax_matchesNull(v___x_1387_, v___x_481_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_P_1391_; 
v___x_1389_ = lean_unsigned_to_nat(4u);
v___x_1390_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1369_);
v_P_1391_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1389_);
lean_dec(v___x_483_);
if (v___x_1312_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1390_;
v_____discr_944_ = v_P_1391_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1351_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1390_;
v_____discr_944_ = v_P_1391_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1371_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1390_;
v_____discr_944_ = v_P_1391_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1388_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1390_;
v_____discr_944_ = v_P_1391_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1392_; 
lean_inc(v___x_1390_);
v___x_1392_ = l_Lean_Syntax_matchesNull(v___x_1390_, v___x_481_);
if (v___x_1392_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1390_;
v_____discr_944_ = v_P_1391_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_ty_1398_; lean_object* v_xs_1399_; 
lean_dec(v___x_1390_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1393_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1394_ = l_Array_extract___redArg(v___x_1393_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1396_ = lean_box(2);
v___x_1397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___x_1395_);
lean_ctor_set(v___x_1397_, 2, v___x_1394_);
v_ty_1398_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_482_);
lean_dec(v___x_1370_);
v_xs_1399_ = l_Lean_Syntax_getArgs(v___x_1397_);
lean_dec_ref(v___x_1397_);
v_x_878_ = v_x_1349_;
v_xs_879_ = v_xs_1399_;
v_ty_880_ = v_ty_1398_;
v_P_881_ = v_P_1391_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1400_ = lean_unsigned_to_nat(4u);
v___x_1401_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1369_);
lean_inc(v___x_1401_);
v___x_1402_ = l_Lean_Syntax_matchesNull(v___x_1401_, v___x_481_);
if (v___x_1402_ == 0)
{
lean_object* v_P_1403_; 
v_P_1403_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1400_);
lean_dec(v___x_483_);
if (v___x_1312_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1401_;
v_____discr_944_ = v_P_1403_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1351_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1401_;
v_____discr_944_ = v_P_1403_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1371_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1401_;
v_____discr_944_ = v_P_1403_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1388_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1401_;
v_____discr_944_ = v_P_1403_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1402_ == 0)
{
lean_dec(v___x_1370_);
lean_dec(v_x_1349_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1401_;
v_____discr_944_ = v_P_1403_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_ty_1409_; lean_object* v_xs_1410_; 
lean_dec(v___x_1401_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1404_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1405_ = l_Array_extract___redArg(v___x_1404_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1407_ = lean_box(2);
v___x_1408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v___x_1406_);
lean_ctor_set(v___x_1408_, 2, v___x_1405_);
v_ty_1409_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_482_);
lean_dec(v___x_1370_);
v_xs_1410_ = l_Lean_Syntax_getArgs(v___x_1408_);
lean_dec_ref(v___x_1408_);
v_x_878_ = v_x_1349_;
v_xs_879_ = v_xs_1410_;
v_ty_880_ = v_ty_1409_;
v_P_881_ = v_P_1403_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1411_; lean_object* v_P_1412_; 
lean_dec(v___x_1401_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_ty_1411_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_482_);
lean_dec(v___x_1370_);
v_P_1412_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1400_);
lean_dec(v___x_483_);
v_x_825_ = v_x_1349_;
v_ty_826_ = v_ty_1411_;
v_P_827_ = v_P_1412_;
v___y_828_ = v_a_471_;
v___y_829_ = v_a_472_;
goto v___jp_824_;
}
}
}
}
}
}
else
{
lean_object* v_x_1413_; uint8_t v___x_1414_; 
v_x_1413_ = l_Lean_Syntax_getArg(v___x_1310_, v___x_481_);
lean_inc(v_x_1413_);
v___x_1414_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_822_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_P_1421_; uint8_t v___x_1422_; 
v___x_1415_ = lean_unsigned_to_nat(2u);
v___x_1416_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1415_);
v___x_1417_ = lean_unsigned_to_nat(3u);
v___x_1418_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1417_);
v___x_1419_ = lean_unsigned_to_nat(4u);
v___x_1420_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1415_);
v_P_1421_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1419_);
lean_dec(v___x_483_);
lean_inc(v___x_1310_);
v___x_1422_ = l_Lean_Syntax_matchesNull(v___x_1310_, v___x_482_);
if (v___x_1422_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1424_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1425_; 
lean_inc(v___x_1416_);
v___x_1425_ = l_Lean_Syntax_matchesNull(v___x_1416_, v___x_1415_);
if (v___x_1425_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = l_Lean_Syntax_matchesNull(v___x_1418_, v___x_481_);
if (v___x_1426_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1427_; 
lean_inc(v___x_1420_);
v___x_1427_ = l_Lean_Syntax_matchesNull(v___x_1420_, v___x_481_);
if (v___x_1427_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_ty_1433_; lean_object* v_xs_1434_; 
lean_dec(v___x_1420_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1428_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1429_ = l_Array_extract___redArg(v___x_1428_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1428_);
v___x_1430_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1431_ = lean_box(2);
v___x_1432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v___x_1430_);
lean_ctor_set(v___x_1432_, 2, v___x_1429_);
v_ty_1433_ = l_Lean_Syntax_getArg(v___x_1416_, v___x_482_);
lean_dec(v___x_1416_);
v_xs_1434_ = l_Lean_Syntax_getArgs(v___x_1432_);
lean_dec_ref(v___x_1432_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1434_;
v_ty_880_ = v_ty_1433_;
v_P_881_ = v_P_1421_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1436_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1435_);
if (v___x_1436_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1436_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1437_; 
lean_inc(v___x_1416_);
v___x_1437_ = l_Lean_Syntax_matchesNull(v___x_1416_, v___x_1415_);
if (v___x_1437_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = l_Lean_Syntax_matchesNull(v___x_1418_, v___x_481_);
if (v___x_1438_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1439_; 
lean_inc(v___x_1420_);
v___x_1439_ = l_Lean_Syntax_matchesNull(v___x_1420_, v___x_481_);
if (v___x_1439_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v_ty_1445_; lean_object* v_xs_1446_; 
lean_dec(v___x_1420_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1440_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1441_ = l_Array_extract___redArg(v___x_1440_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1443_ = lean_box(2);
v___x_1444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___x_1442_);
lean_ctor_set(v___x_1444_, 2, v___x_1441_);
v_ty_1445_ = l_Lean_Syntax_getArg(v___x_1416_, v___x_482_);
lean_dec(v___x_1416_);
v_xs_1446_ = l_Lean_Syntax_getArgs(v___x_1444_);
lean_dec_ref(v___x_1444_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1446_;
v_ty_880_ = v_ty_1445_;
v_P_881_ = v_P_1421_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
uint8_t v___x_1447_; 
lean_inc(v___x_1416_);
v___x_1447_ = l_Lean_Syntax_matchesNull(v___x_1416_, v___x_1415_);
if (v___x_1447_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1436_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1447_ == 0)
{
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = l_Lean_Syntax_matchesNull(v___x_1418_, v___x_481_);
if (v___x_1448_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1449_; 
lean_inc(v___x_1420_);
v___x_1449_ = l_Lean_Syntax_matchesNull(v___x_1420_, v___x_481_);
if (v___x_1449_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_ty_1455_; lean_object* v_xs_1456_; 
lean_dec(v___x_1420_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1450_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1451_ = l_Array_extract___redArg(v___x_1450_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1453_ = lean_box(2);
v___x_1454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___x_1452_);
lean_ctor_set(v___x_1454_, 2, v___x_1451_);
v_ty_1455_ = l_Lean_Syntax_getArg(v___x_1416_, v___x_482_);
lean_dec(v___x_1416_);
v_xs_1456_ = l_Lean_Syntax_getArgs(v___x_1454_);
lean_dec_ref(v___x_1454_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1456_;
v_ty_880_ = v_ty_1455_;
v_P_881_ = v_P_1421_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Lean_Syntax_matchesNull(v___x_1418_, v___x_481_);
if (v___x_1457_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1436_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1447_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1457_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1458_; 
lean_inc(v___x_1420_);
v___x_1458_ = l_Lean_Syntax_matchesNull(v___x_1420_, v___x_481_);
if (v___x_1458_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_ty_1464_; lean_object* v_xs_1465_; 
lean_dec(v___x_1420_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1459_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1460_ = l_Array_extract___redArg(v___x_1459_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1462_ = lean_box(2);
v___x_1463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v___x_1460_);
v_ty_1464_ = l_Lean_Syntax_getArg(v___x_1416_, v___x_482_);
lean_dec(v___x_1416_);
v_xs_1465_ = l_Lean_Syntax_getArgs(v___x_1463_);
lean_dec_ref(v___x_1463_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1465_;
v_ty_880_ = v_ty_1464_;
v_P_881_ = v_P_1421_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
uint8_t v___x_1466_; 
lean_inc(v___x_1420_);
v___x_1466_ = l_Lean_Syntax_matchesNull(v___x_1420_, v___x_481_);
if (v___x_1466_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1436_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1447_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1457_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1466_ == 0)
{
lean_dec(v___x_1416_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1420_;
v_____discr_944_ = v_P_1421_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_ty_1472_; lean_object* v_xs_1473_; 
lean_dec(v___x_1420_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1467_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1468_ = l_Array_extract___redArg(v___x_1467_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1467_);
v___x_1469_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1470_ = lean_box(2);
v___x_1471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v___x_1468_);
v_ty_1472_ = l_Lean_Syntax_getArg(v___x_1416_, v___x_482_);
lean_dec(v___x_1416_);
v_xs_1473_ = l_Lean_Syntax_getArgs(v___x_1471_);
lean_dec_ref(v___x_1471_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1473_;
v_ty_880_ = v_ty_1472_;
v_P_881_ = v_P_1421_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1474_; 
lean_dec(v___x_1420_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_ty_1474_ = l_Lean_Syntax_getArg(v___x_1416_, v___x_482_);
lean_dec(v___x_1416_);
v_x_825_ = v_x_1413_;
v_ty_826_ = v_ty_1474_;
v_P_827_ = v_P_1421_;
v___y_828_ = v_a_471_;
v___y_829_ = v_a_472_;
goto v___jp_824_;
}
}
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = lean_unsigned_to_nat(2u);
v___x_1476_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1475_);
lean_inc(v___x_1476_);
v___x_1477_ = l_Lean_Syntax_matchesNull(v___x_1476_, v___x_1475_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_P_1482_; uint8_t v___x_1483_; 
v___x_1478_ = lean_unsigned_to_nat(3u);
v___x_1479_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1478_);
v___x_1480_ = lean_unsigned_to_nat(4u);
v___x_1481_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1475_);
v_P_1482_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1480_);
lean_dec(v___x_483_);
lean_inc(v___x_1310_);
v___x_1483_ = l_Lean_Syntax_matchesNull(v___x_1310_, v___x_482_);
if (v___x_1483_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1485_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = l_Lean_Syntax_matchesNull(v___x_1479_, v___x_481_);
if (v___x_1486_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1487_; 
lean_inc(v___x_1481_);
v___x_1487_ = l_Lean_Syntax_matchesNull(v___x_1481_, v___x_481_);
if (v___x_1487_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v_ty_1493_; lean_object* v_xs_1494_; 
lean_dec(v___x_1481_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1488_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1489_ = l_Array_extract___redArg(v___x_1488_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1491_ = lean_box(2);
v___x_1492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v___x_1489_);
v_ty_1493_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1494_ = l_Lean_Syntax_getArgs(v___x_1492_);
lean_dec_ref(v___x_1492_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1494_;
v_ty_880_ = v_ty_1493_;
v_P_881_ = v_P_1482_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1496_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1495_);
if (v___x_1496_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1496_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_Syntax_matchesNull(v___x_1479_, v___x_481_);
if (v___x_1497_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1498_; 
lean_inc(v___x_1481_);
v___x_1498_ = l_Lean_Syntax_matchesNull(v___x_1481_, v___x_481_);
if (v___x_1498_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v_ty_1504_; lean_object* v_xs_1505_; 
lean_dec(v___x_1481_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1499_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1500_ = l_Array_extract___redArg(v___x_1499_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1502_ = lean_box(2);
v___x_1503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v___x_1501_);
lean_ctor_set(v___x_1503_, 2, v___x_1500_);
v_ty_1504_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1505_ = l_Lean_Syntax_getArgs(v___x_1503_);
lean_dec_ref(v___x_1503_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1505_;
v_ty_880_ = v_ty_1504_;
v_P_881_ = v_P_1482_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
if (v___x_1477_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1496_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = l_Lean_Syntax_matchesNull(v___x_1479_, v___x_481_);
if (v___x_1506_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1507_; 
lean_inc(v___x_1481_);
v___x_1507_ = l_Lean_Syntax_matchesNull(v___x_1481_, v___x_481_);
if (v___x_1507_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_ty_1513_; lean_object* v_xs_1514_; 
lean_dec(v___x_1481_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1508_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1509_ = l_Array_extract___redArg(v___x_1508_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1508_);
v___x_1510_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1511_ = lean_box(2);
v___x_1512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1510_);
lean_ctor_set(v___x_1512_, 2, v___x_1509_);
v_ty_1513_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1514_ = l_Lean_Syntax_getArgs(v___x_1512_);
lean_dec_ref(v___x_1512_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1514_;
v_ty_880_ = v_ty_1513_;
v_P_881_ = v_P_1482_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = l_Lean_Syntax_matchesNull(v___x_1479_, v___x_481_);
if (v___x_1515_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1496_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1515_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1516_; 
lean_inc(v___x_1481_);
v___x_1516_ = l_Lean_Syntax_matchesNull(v___x_1481_, v___x_481_);
if (v___x_1516_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_ty_1522_; lean_object* v_xs_1523_; 
lean_dec(v___x_1481_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1517_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1518_ = l_Array_extract___redArg(v___x_1517_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1520_ = lean_box(2);
v___x_1521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
lean_ctor_set(v___x_1521_, 2, v___x_1518_);
v_ty_1522_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1523_ = l_Lean_Syntax_getArgs(v___x_1521_);
lean_dec_ref(v___x_1521_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1523_;
v_ty_880_ = v_ty_1522_;
v_P_881_ = v_P_1482_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
uint8_t v___x_1524_; 
lean_inc(v___x_1481_);
v___x_1524_ = l_Lean_Syntax_matchesNull(v___x_1481_, v___x_481_);
if (v___x_1524_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1496_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1515_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1524_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1481_;
v_____discr_944_ = v_P_1482_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_ty_1530_; lean_object* v_xs_1531_; 
lean_dec(v___x_1481_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1525_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1526_ = l_Array_extract___redArg(v___x_1525_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1528_ = lean_box(2);
v___x_1529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___x_1527_);
lean_ctor_set(v___x_1529_, 2, v___x_1526_);
v_ty_1530_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1531_ = l_Lean_Syntax_getArgs(v___x_1529_);
lean_dec_ref(v___x_1529_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1531_;
v_ty_880_ = v_ty_1530_;
v_P_881_ = v_P_1482_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1532_; 
lean_dec(v___x_1481_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_ty_1532_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_x_825_ = v_x_1413_;
v_ty_826_ = v_ty_1532_;
v_P_827_ = v_P_1482_;
v___y_828_ = v_a_471_;
v___y_829_ = v_a_472_;
goto v___jp_824_;
}
}
}
}
}
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_unsigned_to_nat(3u);
v___x_1534_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1533_);
v___x_1535_ = l_Lean_Syntax_matchesNull(v___x_1534_, v___x_481_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_P_1538_; uint8_t v___x_1539_; 
v___x_1536_ = lean_unsigned_to_nat(4u);
v___x_1537_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1475_);
v_P_1538_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1536_);
lean_dec(v___x_483_);
lean_inc(v___x_1310_);
v___x_1539_ = l_Lean_Syntax_matchesNull(v___x_1310_, v___x_482_);
if (v___x_1539_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1541_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1542_; 
lean_inc(v___x_1537_);
v___x_1542_ = l_Lean_Syntax_matchesNull(v___x_1537_, v___x_481_);
if (v___x_1542_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_ty_1548_; lean_object* v_xs_1549_; 
lean_dec(v___x_1537_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1543_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1544_ = l_Array_extract___redArg(v___x_1543_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1546_ = lean_box(2);
v___x_1547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1545_);
lean_ctor_set(v___x_1547_, 2, v___x_1544_);
v_ty_1548_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1549_ = l_Lean_Syntax_getArgs(v___x_1547_);
lean_dec_ref(v___x_1547_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1549_;
v_ty_880_ = v_ty_1548_;
v_P_881_ = v_P_1538_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1551_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1550_);
if (v___x_1551_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1551_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1552_; 
lean_inc(v___x_1537_);
v___x_1552_ = l_Lean_Syntax_matchesNull(v___x_1537_, v___x_481_);
if (v___x_1552_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_ty_1558_; lean_object* v_xs_1559_; 
lean_dec(v___x_1537_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1553_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1554_ = l_Array_extract___redArg(v___x_1553_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1556_ = lean_box(2);
v___x_1557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___x_1555_);
lean_ctor_set(v___x_1557_, 2, v___x_1554_);
v_ty_1558_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1559_ = l_Lean_Syntax_getArgs(v___x_1557_);
lean_dec_ref(v___x_1557_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1559_;
v_ty_880_ = v_ty_1558_;
v_P_881_ = v_P_1538_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
if (v___x_1477_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1551_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1560_; 
lean_inc(v___x_1537_);
v___x_1560_ = l_Lean_Syntax_matchesNull(v___x_1537_, v___x_481_);
if (v___x_1560_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v_ty_1566_; lean_object* v_xs_1567_; 
lean_dec(v___x_1537_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1561_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1562_ = l_Array_extract___redArg(v___x_1561_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1564_ = lean_box(2);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1563_);
lean_ctor_set(v___x_1565_, 2, v___x_1562_);
v_ty_1566_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1567_ = l_Lean_Syntax_getArgs(v___x_1565_);
lean_dec_ref(v___x_1565_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1567_;
v_ty_880_ = v_ty_1566_;
v_P_881_ = v_P_1538_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
if (v___x_1535_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1551_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
uint8_t v___x_1568_; 
lean_inc(v___x_1537_);
v___x_1568_ = l_Lean_Syntax_matchesNull(v___x_1537_, v___x_481_);
if (v___x_1568_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_ty_1574_; lean_object* v_xs_1575_; 
lean_dec(v___x_1537_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1569_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1570_ = l_Array_extract___redArg(v___x_1569_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1572_ = lean_box(2);
v___x_1573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___x_1571_);
lean_ctor_set(v___x_1573_, 2, v___x_1570_);
v_ty_1574_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1575_ = l_Lean_Syntax_getArgs(v___x_1573_);
lean_dec_ref(v___x_1573_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1575_;
v_ty_880_ = v_ty_1574_;
v_P_881_ = v_P_1538_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
uint8_t v___x_1576_; 
lean_inc(v___x_1537_);
v___x_1576_ = l_Lean_Syntax_matchesNull(v___x_1537_, v___x_481_);
if (v___x_1576_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1551_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1576_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1537_;
v_____discr_944_ = v_P_1538_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_ty_1582_; lean_object* v_xs_1583_; 
lean_dec(v___x_1537_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1577_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1578_ = l_Array_extract___redArg(v___x_1577_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1580_ = lean_box(2);
v___x_1581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v___x_1579_);
lean_ctor_set(v___x_1581_, 2, v___x_1578_);
v_ty_1582_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1583_ = l_Lean_Syntax_getArgs(v___x_1581_);
lean_dec_ref(v___x_1581_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1583_;
v_ty_880_ = v_ty_1582_;
v_P_881_ = v_P_1538_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1584_; 
lean_dec(v___x_1537_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_ty_1584_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_x_825_ = v_x_1413_;
v_ty_826_ = v_ty_1584_;
v_P_827_ = v_P_1538_;
v___y_828_ = v_a_471_;
v___y_829_ = v_a_472_;
goto v___jp_824_;
}
}
}
}
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_unsigned_to_nat(4u);
v___x_1586_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1475_);
lean_inc(v___x_1586_);
v___x_1587_ = l_Lean_Syntax_matchesNull(v___x_1586_, v___x_481_);
if (v___x_1587_ == 0)
{
lean_object* v_P_1588_; uint8_t v___x_1589_; 
v_P_1588_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1585_);
lean_dec(v___x_483_);
lean_inc(v___x_1310_);
v___x_1589_ = l_Lean_Syntax_matchesNull(v___x_1310_, v___x_482_);
if (v___x_1589_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1591_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1587_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_ty_1597_; lean_object* v_xs_1598_; 
lean_dec(v___x_1586_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1592_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1593_ = l_Array_extract___redArg(v___x_1592_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1595_ = lean_box(2);
v___x_1596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v___x_1594_);
lean_ctor_set(v___x_1596_, 2, v___x_1593_);
v_ty_1597_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1598_ = l_Lean_Syntax_getArgs(v___x_1596_);
lean_dec_ref(v___x_1596_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1598_;
v_ty_880_ = v_ty_1597_;
v_P_881_ = v_P_1588_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1413_);
v___x_1600_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1599_);
if (v___x_1600_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1600_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1587_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v_ty_1606_; lean_object* v_xs_1607_; 
lean_dec(v___x_1586_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1601_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1602_ = l_Array_extract___redArg(v___x_1601_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1604_ = lean_box(2);
v___x_1605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v___x_1603_);
lean_ctor_set(v___x_1605_, 2, v___x_1602_);
v_ty_1606_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1607_ = l_Lean_Syntax_getArgs(v___x_1605_);
lean_dec_ref(v___x_1605_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1607_;
v_ty_880_ = v_ty_1606_;
v_P_881_ = v_P_1588_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
if (v___x_1477_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1600_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1587_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_ty_1613_; lean_object* v_xs_1614_; 
lean_dec(v___x_1586_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1608_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1609_ = l_Array_extract___redArg(v___x_1608_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1608_);
v___x_1610_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1611_ = lean_box(2);
v___x_1612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v___x_1610_);
lean_ctor_set(v___x_1612_, 2, v___x_1609_);
v_ty_1613_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1614_ = l_Lean_Syntax_getArgs(v___x_1612_);
lean_dec_ref(v___x_1612_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1614_;
v_ty_880_ = v_ty_1613_;
v_P_881_ = v_P_1588_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
if (v___x_1535_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1600_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1587_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v_ty_1620_; lean_object* v_xs_1621_; 
lean_dec(v___x_1586_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1615_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1616_ = l_Array_extract___redArg(v___x_1615_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1618_ = lean_box(2);
v___x_1619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___x_1617_);
lean_ctor_set(v___x_1619_, 2, v___x_1616_);
v_ty_1620_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1621_ = l_Lean_Syntax_getArgs(v___x_1619_);
lean_dec_ref(v___x_1619_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1621_;
v_ty_880_ = v_ty_1620_;
v_P_881_ = v_P_1588_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
if (v___x_1587_ == 0)
{
if (v___x_1312_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1600_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1477_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1535_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
if (v___x_1587_ == 0)
{
lean_dec(v___x_1476_);
lean_dec(v_x_1413_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v_____discr_943_ = v___x_1586_;
v_____discr_944_ = v_P_1588_;
v___y_945_ = v_a_471_;
v___y_946_ = v_a_472_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_ty_1627_; lean_object* v_xs_1628_; 
lean_dec(v___x_1586_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___x_1622_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1623_ = l_Array_extract___redArg(v___x_1622_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1625_ = lean_box(2);
v___x_1626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v___x_1624_);
lean_ctor_set(v___x_1626_, 2, v___x_1623_);
v_ty_1627_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_xs_1628_ = l_Lean_Syntax_getArgs(v___x_1626_);
lean_dec_ref(v___x_1626_);
v_x_878_ = v_x_1413_;
v_xs_879_ = v_xs_1628_;
v_ty_880_ = v_ty_1627_;
v_P_881_ = v_P_1588_;
v___y_882_ = v_a_471_;
v___y_883_ = v_a_472_;
goto v___jp_877_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1629_; 
lean_dec(v___x_1586_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_ty_1629_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v_x_825_ = v_x_1413_;
v_ty_826_ = v_ty_1629_;
v_P_827_ = v_P_1588_;
v___y_828_ = v_a_471_;
v___y_829_ = v_a_472_;
goto v___jp_824_;
}
}
}
}
}
}
else
{
lean_object* v_quotContext_1630_; lean_object* v_currMacroScope_1631_; lean_object* v_ref_1632_; lean_object* v_tk_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_xs_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v___x_1586_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_quotContext_1630_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1631_ = lean_ctor_get(v_a_471_, 2);
v_ref_1632_ = lean_ctor_get(v_a_471_, 5);
v_tk_1633_ = l_Lean_Syntax_getArg(v_x_1413_, v___x_481_);
lean_dec(v_x_1413_);
v___x_1634_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1635_ = l_Array_extract___redArg(v___x_1634_, v___x_482_, v___x_1311_);
lean_dec_ref(v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1637_ = lean_box(2);
v___x_1638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___x_1636_);
lean_ctor_set(v___x_1638_, 2, v___x_1635_);
v___x_1639_ = l_Lean_Syntax_getArg(v___x_1476_, v___x_482_);
lean_dec(v___x_1476_);
v___x_1640_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1585_);
lean_dec(v___x_483_);
v_xs_1641_ = l_Lean_Syntax_getArgs(v___x_1638_);
lean_dec_ref(v___x_1638_);
v___x_1642_ = l_Lean_SourceInfo_fromRef(v_ref_1632_, v___x_823_);
v___x_1643_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1644_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1645_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1631_, 2);
lean_inc_n(v_quotContext_1630_, 2);
v___x_1646_ = l_Lean_addMacroScope(v_quotContext_1630_, v___x_1645_, v_currMacroScope_1631_);
v___x_1647_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1642_, 27);
v___x_1648_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1642_);
lean_ctor_set(v___x_1648_, 1, v___x_1644_);
lean_ctor_set(v___x_1648_, 2, v___x_1646_);
lean_ctor_set(v___x_1648_, 3, v___x_1647_);
v___x_1649_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1650_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1651_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1642_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1654_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1655_ = lean_box(0);
v___x_1656_ = l_Lean_addMacroScope(v_quotContext_1630_, v___x_1655_, v_currMacroScope_1631_);
v___x_1657_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1658_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1642_);
lean_ctor_set(v___x_1658_, 1, v___x_1654_);
lean_ctor_set(v___x_1658_, 2, v___x_1656_);
lean_ctor_set(v___x_1658_, 3, v___x_1657_);
v___x_1659_ = l_Lean_Syntax_node1(v___x_1642_, v___x_1653_, v___x_1658_);
lean_inc_ref(v___x_1652_);
v___x_1660_ = l_Lean_Syntax_node2(v___x_1642_, v___x_1650_, v___x_1652_, v___x_1659_);
v___x_1661_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1662_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1642_);
lean_ctor_set(v___x_1663_, 1, v___x_1661_);
v___x_1664_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1665_ = l_Lean_SourceInfo_fromRef(v_tk_1633_, v___x_688_);
lean_dec(v_tk_1633_);
v___x_1666_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_Syntax_node1(v___x_1642_, v___x_822_, v___x_1667_);
v___x_1669_ = l_Lean_Syntax_node1(v___x_1642_, v___x_1636_, v___x_1668_);
v___x_1670_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_1671_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1642_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
lean_inc(v___x_1639_);
lean_inc_ref(v___x_1672_);
v___x_1673_ = l_Lean_Syntax_node2(v___x_1642_, v___x_1670_, v___x_1672_, v___x_1639_);
v___x_1674_ = l_Lean_Syntax_node1(v___x_1642_, v___x_1636_, v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1642_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1642_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_1680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1642_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1682_ = l_Array_append___redArg(v___x_1681_, v_xs_1641_);
lean_dec_ref(v_xs_1641_);
v___x_1683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1642_);
lean_ctor_set(v___x_1683_, 1, v___x_1636_);
lean_ctor_set(v___x_1683_, 2, v___x_1682_);
v___x_1684_ = l_Lean_Syntax_node2(v___x_1642_, v___x_1636_, v___x_1672_, v___x_1639_);
v___x_1685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1642_);
lean_ctor_set(v___x_1685_, 1, v___x_1636_);
lean_ctor_set(v___x_1685_, 2, v___x_1681_);
v___x_1686_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1642_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
lean_inc_ref_n(v___x_1687_, 2);
lean_inc_ref(v___x_1685_);
v___x_1688_ = l_Lean_Syntax_node5(v___x_1642_, v___x_876_, v___x_1652_, v___x_1683_, v___x_1684_, v___x_1685_, v___x_1687_);
v___x_1689_ = l_Lean_Syntax_node1(v___x_1642_, v___x_1636_, v___x_1688_);
v___x_1690_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_1691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1642_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = l_Lean_Syntax_node5(v___x_1642_, v___x_496_, v___x_1680_, v___x_1689_, v___x_1685_, v___x_1691_, v___x_1640_);
v___x_1693_ = l_Lean_Syntax_node3(v___x_1642_, v___x_477_, v___x_1678_, v___x_1692_, v___x_1687_);
v___x_1694_ = l_Lean_Syntax_node4(v___x_1642_, v___x_1664_, v___x_1669_, v___x_1674_, v___x_1676_, v___x_1693_);
v___x_1695_ = l_Lean_Syntax_node2(v___x_1642_, v___x_1662_, v___x_1663_, v___x_1694_);
v___x_1696_ = l_Lean_Syntax_node3(v___x_1642_, v___x_1649_, v___x_1660_, v___x_1695_, v___x_1687_);
v___x_1697_ = l_Lean_Syntax_node1(v___x_1642_, v___x_1636_, v___x_1696_);
v___x_1698_ = l_Lean_Syntax_node2(v___x_1642_, v___x_1643_, v___x_1648_, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v_a_472_);
return v___x_1699_;
}
}
}
}
}
}
v___jp_877_:
{
lean_object* v_quotContext_884_; lean_object* v_currMacroScope_885_; lean_object* v_ref_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_quotContext_884_ = lean_ctor_get(v___y_882_, 1);
v_currMacroScope_885_ = lean_ctor_get(v___y_882_, 2);
v_ref_886_ = lean_ctor_get(v___y_882_, 5);
v___x_887_ = l_Lean_SourceInfo_fromRef(v_ref_886_, v___x_823_);
v___x_888_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_889_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_890_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_885_, 2);
lean_inc_n(v_quotContext_884_, 2);
v___x_891_ = l_Lean_addMacroScope(v_quotContext_884_, v___x_890_, v_currMacroScope_885_);
v___x_892_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_887_, 26);
v___x_893_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_893_, 0, v___x_887_);
lean_ctor_set(v___x_893_, 1, v___x_889_);
lean_ctor_set(v___x_893_, 2, v___x_891_);
lean_ctor_set(v___x_893_, 3, v___x_892_);
v___x_894_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_895_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_896_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_897_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_887_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_900_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_901_ = lean_box(0);
v___x_902_ = l_Lean_addMacroScope(v_quotContext_884_, v___x_901_, v_currMacroScope_885_);
v___x_903_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_904_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_904_, 0, v___x_887_);
lean_ctor_set(v___x_904_, 1, v___x_900_);
lean_ctor_set(v___x_904_, 2, v___x_902_);
lean_ctor_set(v___x_904_, 3, v___x_903_);
v___x_905_ = l_Lean_Syntax_node1(v___x_887_, v___x_899_, v___x_904_);
lean_inc_ref(v___x_898_);
v___x_906_ = l_Lean_Syntax_node2(v___x_887_, v___x_896_, v___x_898_, v___x_905_);
v___x_907_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_908_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_887_);
lean_ctor_set(v___x_909_, 1, v___x_907_);
v___x_910_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_911_ = l_Lean_Syntax_node1(v___x_887_, v___x_894_, v_x_878_);
v___x_912_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_913_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_887_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
lean_inc(v_ty_880_);
lean_inc_ref(v___x_914_);
v___x_915_ = l_Lean_Syntax_node2(v___x_887_, v___x_912_, v___x_914_, v_ty_880_);
v___x_916_ = l_Lean_Syntax_node1(v___x_887_, v___x_894_, v___x_915_);
v___x_917_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_887_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_887_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_887_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_924_ = l_Array_append___redArg(v___x_923_, v_xs_879_);
lean_dec_ref(v_xs_879_);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_887_);
lean_ctor_set(v___x_925_, 1, v___x_894_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
v___x_926_ = l_Lean_Syntax_node2(v___x_887_, v___x_894_, v___x_914_, v_ty_880_);
v___x_927_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_927_, 0, v___x_887_);
lean_ctor_set(v___x_927_, 1, v___x_894_);
lean_ctor_set(v___x_927_, 2, v___x_923_);
v___x_928_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_887_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
lean_inc_ref_n(v___x_929_, 2);
lean_inc_ref(v___x_927_);
v___x_930_ = l_Lean_Syntax_node5(v___x_887_, v___x_876_, v___x_898_, v___x_925_, v___x_926_, v___x_927_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node1(v___x_887_, v___x_894_, v___x_930_);
v___x_932_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_887_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_Syntax_node5(v___x_887_, v___x_496_, v___x_922_, v___x_931_, v___x_927_, v___x_933_, v_P_881_);
v___x_935_ = l_Lean_Syntax_node3(v___x_887_, v___x_477_, v___x_920_, v___x_934_, v___x_929_);
v___x_936_ = l_Lean_Syntax_node4(v___x_887_, v___x_910_, v___x_911_, v___x_916_, v___x_918_, v___x_935_);
v___x_937_ = l_Lean_Syntax_node2(v___x_887_, v___x_908_, v___x_909_, v___x_936_);
v___x_938_ = l_Lean_Syntax_node3(v___x_887_, v___x_895_, v___x_906_, v___x_937_, v___x_929_);
v___x_939_ = l_Lean_Syntax_node1(v___x_887_, v___x_894_, v___x_938_);
v___x_940_ = l_Lean_Syntax_node2(v___x_887_, v___x_888_, v___x_893_, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___y_883_);
return v___x_941_;
}
v___jp_942_:
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = l_Lean_Syntax_getNumArgs(v___x_687_);
v___x_948_ = lean_nat_dec_le(v___x_482_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_821_);
v___x_950_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_949_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; 
lean_inc(v_x_821_);
v___x_951_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_876_);
if (v___x_951_ == 0)
{
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = l_Lean_Syntax_getArg(v_x_821_, v___x_482_);
lean_inc(v___x_952_);
v___x_953_ = l_Lean_Syntax_matchesNull(v___x_952_, v___x_482_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = l_Lean_Syntax_getNumArgs(v___x_952_);
v___x_955_ = lean_nat_dec_le(v___x_482_, v___x_954_);
if (v___x_955_ == 0)
{
lean_dec(v___x_954_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v_x_956_; uint8_t v___x_957_; 
v_x_956_ = l_Lean_Syntax_getArg(v___x_952_, v___x_481_);
lean_inc(v_x_956_);
v___x_957_ = l_Lean_Syntax_isOfKind(v_x_956_, v___x_949_);
if (v___x_957_ == 0)
{
lean_dec(v_x_956_);
lean_dec(v___x_954_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = lean_unsigned_to_nat(2u);
v___x_959_ = l_Lean_Syntax_getArg(v_x_821_, v___x_958_);
lean_inc(v___x_959_);
v___x_960_ = l_Lean_Syntax_matchesNull(v___x_959_, v___x_958_);
if (v___x_960_ == 0)
{
lean_dec(v___x_959_);
lean_dec(v_x_956_);
lean_dec(v___x_954_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_961_ = lean_unsigned_to_nat(3u);
v___x_962_ = l_Lean_Syntax_getArg(v_x_821_, v___x_961_);
lean_dec(v_x_821_);
v___x_963_ = l_Lean_Syntax_matchesNull(v___x_962_, v___x_481_);
if (v___x_963_ == 0)
{
lean_dec(v___x_959_);
lean_dec(v_x_956_);
lean_dec(v___x_954_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = l_Lean_Syntax_matchesNull(v_____discr_943_, v___x_481_);
if (v___x_964_ == 0)
{
lean_dec(v___x_959_);
lean_dec(v_x_956_);
lean_dec(v___x_954_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_ty_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_ys_974_; lean_object* v_xs_975_; 
v___x_965_ = l_Lean_Syntax_getArgs(v___x_952_);
lean_dec(v___x_952_);
v___x_966_ = l_Array_extract___redArg(v___x_965_, v___x_482_, v___x_954_);
lean_dec_ref(v___x_965_);
v_ty_967_ = l_Lean_Syntax_getArg(v___x_959_, v___x_482_);
lean_dec(v___x_959_);
v___x_968_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_969_ = lean_box(2);
v___x_970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set(v___x_970_, 2, v___x_966_);
v___x_971_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_972_ = l_Array_extract___redArg(v___x_971_, v___x_482_, v___x_947_);
lean_dec_ref(v___x_971_);
v___x_973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_969_);
lean_ctor_set(v___x_973_, 1, v___x_968_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
v_ys_974_ = l_Lean_Syntax_getArgs(v___x_973_);
lean_dec_ref(v___x_973_);
v_xs_975_ = l_Lean_Syntax_getArgs(v___x_970_);
lean_dec_ref(v___x_970_);
v_x_616_ = v_x_956_;
v_xs_617_ = v_xs_975_;
v_ty_618_ = v_ty_967_;
v_ys_619_ = v_ys_974_;
v_P_620_ = v_____discr_944_;
v___y_621_ = v___y_945_;
v___y_622_ = v___y_946_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_x_976_; uint8_t v___x_977_; 
v_x_976_ = l_Lean_Syntax_getArg(v___x_952_, v___x_481_);
lean_inc(v_x_976_);
v___x_977_ = l_Lean_Syntax_isOfKind(v_x_976_, v___x_949_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = l_Lean_Syntax_getNumArgs(v___x_952_);
v___x_979_ = lean_nat_dec_le(v___x_482_, v___x_978_);
if (v___x_979_ == 0)
{
lean_dec(v___x_978_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_977_ == 0)
{
lean_dec(v___x_978_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_unsigned_to_nat(2u);
v___x_981_ = l_Lean_Syntax_getArg(v_x_821_, v___x_980_);
lean_inc(v___x_981_);
v___x_982_ = l_Lean_Syntax_matchesNull(v___x_981_, v___x_980_);
if (v___x_982_ == 0)
{
lean_dec(v___x_981_);
lean_dec(v___x_978_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_unsigned_to_nat(3u);
v___x_984_ = l_Lean_Syntax_getArg(v_x_821_, v___x_983_);
lean_dec(v_x_821_);
v___x_985_ = l_Lean_Syntax_matchesNull(v___x_984_, v___x_481_);
if (v___x_985_ == 0)
{
lean_dec(v___x_981_);
lean_dec(v___x_978_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Syntax_matchesNull(v_____discr_943_, v___x_481_);
if (v___x_986_ == 0)
{
lean_dec(v___x_981_);
lean_dec(v___x_978_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_ty_995_; lean_object* v_ys_996_; lean_object* v_xs_997_; 
v___x_987_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_988_ = l_Array_extract___redArg(v___x_987_, v___x_482_, v___x_947_);
lean_dec_ref(v___x_987_);
v___x_989_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_990_ = lean_box(2);
v___x_991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_989_);
lean_ctor_set(v___x_991_, 2, v___x_988_);
v___x_992_ = l_Lean_Syntax_getArgs(v___x_952_);
lean_dec(v___x_952_);
v___x_993_ = l_Array_extract___redArg(v___x_992_, v___x_482_, v___x_978_);
lean_dec_ref(v___x_992_);
v___x_994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_994_, 0, v___x_990_);
lean_ctor_set(v___x_994_, 1, v___x_989_);
lean_ctor_set(v___x_994_, 2, v___x_993_);
v_ty_995_ = l_Lean_Syntax_getArg(v___x_981_, v___x_482_);
lean_dec(v___x_981_);
v_ys_996_ = l_Lean_Syntax_getArgs(v___x_991_);
lean_dec_ref(v___x_991_);
v_xs_997_ = l_Lean_Syntax_getArgs(v___x_994_);
lean_dec_ref(v___x_994_);
v_x_616_ = v_x_976_;
v_xs_617_ = v_xs_997_;
v_ty_618_ = v_ty_995_;
v_ys_619_ = v_ys_996_;
v_P_620_ = v_____discr_944_;
v___y_621_ = v___y_945_;
v___y_622_ = v___y_946_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = lean_unsigned_to_nat(2u);
v___x_999_ = l_Lean_Syntax_getArg(v_x_821_, v___x_998_);
lean_inc(v___x_999_);
v___x_1000_ = l_Lean_Syntax_matchesNull(v___x_999_, v___x_998_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = l_Lean_Syntax_getNumArgs(v___x_952_);
v___x_1002_ = lean_nat_dec_le(v___x_482_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_dec(v___x_1001_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_977_ == 0)
{
lean_dec(v___x_1001_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_1000_ == 0)
{
lean_dec(v___x_1001_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(3u);
v___x_1004_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1003_);
lean_dec(v_x_821_);
v___x_1005_ = l_Lean_Syntax_matchesNull(v___x_1004_, v___x_481_);
if (v___x_1005_ == 0)
{
lean_dec(v___x_1001_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = l_Lean_Syntax_matchesNull(v_____discr_943_, v___x_481_);
if (v___x_1006_ == 0)
{
lean_dec(v___x_1001_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_ty_1015_; lean_object* v_ys_1016_; lean_object* v_xs_1017_; 
v___x_1007_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1008_ = l_Array_extract___redArg(v___x_1007_, v___x_482_, v___x_947_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1010_ = lean_box(2);
v___x_1011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
lean_ctor_set(v___x_1011_, 2, v___x_1008_);
v___x_1012_ = l_Lean_Syntax_getArgs(v___x_952_);
lean_dec(v___x_952_);
v___x_1013_ = l_Array_extract___redArg(v___x_1012_, v___x_482_, v___x_1001_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1010_);
lean_ctor_set(v___x_1014_, 1, v___x_1009_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
v_ty_1015_ = l_Lean_Syntax_getArg(v___x_999_, v___x_482_);
lean_dec(v___x_999_);
v_ys_1016_ = l_Lean_Syntax_getArgs(v___x_1011_);
lean_dec_ref(v___x_1011_);
v_xs_1017_ = l_Lean_Syntax_getArgs(v___x_1014_);
lean_dec_ref(v___x_1014_);
v_x_616_ = v_x_976_;
v_xs_617_ = v_xs_1017_;
v_ty_618_ = v_ty_1015_;
v_ys_619_ = v_ys_1016_;
v_P_620_ = v_____discr_944_;
v___y_621_ = v___y_945_;
v___y_622_ = v___y_946_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1018_ = lean_unsigned_to_nat(3u);
v___x_1019_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1018_);
lean_dec(v_x_821_);
v___x_1020_ = l_Lean_Syntax_matchesNull(v___x_1019_, v___x_481_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = l_Lean_Syntax_getNumArgs(v___x_952_);
v___x_1022_ = lean_nat_dec_le(v___x_482_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec(v___x_1021_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_977_ == 0)
{
lean_dec(v___x_1021_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_1000_ == 0)
{
lean_dec(v___x_1021_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_1020_ == 0)
{
lean_dec(v___x_1021_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_____discr_943_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1023_; 
v___x_1023_ = l_Lean_Syntax_matchesNull(v_____discr_943_, v___x_481_);
if (v___x_1023_ == 0)
{
lean_dec(v___x_1021_);
lean_dec(v___x_999_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_ty_1032_; lean_object* v_ys_1033_; lean_object* v_xs_1034_; 
v___x_1024_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1025_ = l_Array_extract___redArg(v___x_1024_, v___x_482_, v___x_947_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1027_ = lean_box(2);
v___x_1028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_1026_);
lean_ctor_set(v___x_1028_, 2, v___x_1025_);
v___x_1029_ = l_Lean_Syntax_getArgs(v___x_952_);
lean_dec(v___x_952_);
v___x_1030_ = l_Array_extract___redArg(v___x_1029_, v___x_482_, v___x_1021_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1027_);
lean_ctor_set(v___x_1031_, 1, v___x_1026_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
v_ty_1032_ = l_Lean_Syntax_getArg(v___x_999_, v___x_482_);
lean_dec(v___x_999_);
v_ys_1033_ = l_Lean_Syntax_getArgs(v___x_1028_);
lean_dec_ref(v___x_1028_);
v_xs_1034_ = l_Lean_Syntax_getArgs(v___x_1031_);
lean_dec_ref(v___x_1031_);
v_x_616_ = v_x_976_;
v_xs_617_ = v_xs_1034_;
v_ty_618_ = v_ty_1032_;
v_ys_619_ = v_ys_1033_;
v_P_620_ = v_____discr_944_;
v___y_621_ = v___y_945_;
v___y_622_ = v___y_946_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_ty_1035_ = l_Lean_Syntax_getArg(v___x_999_, v___x_482_);
lean_dec(v___x_999_);
v___x_1036_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1037_ = l_Array_extract___redArg(v___x_1036_, v___x_482_, v___x_947_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1039_ = lean_box(2);
v___x_1040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_1038_);
lean_ctor_set(v___x_1040_, 2, v___x_1037_);
v___x_1041_ = l_Lean_Syntax_matchesNull(v_____discr_943_, v___x_481_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = l_Lean_Syntax_getNumArgs(v___x_952_);
v___x_1043_ = lean_nat_dec_le(v___x_482_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1040_);
lean_dec(v_ty_1035_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v_____discr_944_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_977_ == 0)
{
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1040_);
lean_dec(v_ty_1035_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v_____discr_944_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_1000_ == 0)
{
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1040_);
lean_dec(v_ty_1035_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v_____discr_944_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_1020_ == 0)
{
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1040_);
lean_dec(v_ty_1035_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v_____discr_944_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
if (v___x_1041_ == 0)
{
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1040_);
lean_dec(v_ty_1035_);
lean_dec(v_x_976_);
lean_dec(v___x_952_);
lean_dec(v_____discr_944_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_ys_1047_; lean_object* v_xs_1048_; 
v___x_1044_ = l_Lean_Syntax_getArgs(v___x_952_);
lean_dec(v___x_952_);
v___x_1045_ = l_Array_extract___redArg(v___x_1044_, v___x_482_, v___x_1042_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1039_);
lean_ctor_set(v___x_1046_, 1, v___x_1038_);
lean_ctor_set(v___x_1046_, 2, v___x_1045_);
v_ys_1047_ = l_Lean_Syntax_getArgs(v___x_1040_);
lean_dec_ref(v___x_1040_);
v_xs_1048_ = l_Lean_Syntax_getArgs(v___x_1046_);
lean_dec_ref(v___x_1046_);
v_x_616_ = v_x_976_;
v_xs_617_ = v_xs_1048_;
v_ty_618_ = v_ty_1035_;
v_ys_619_ = v_ys_1047_;
v_P_620_ = v_____discr_944_;
v___y_621_ = v___y_945_;
v___y_622_ = v___y_946_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1049_; 
lean_dec(v___x_952_);
v_xs_1049_ = l_Lean_Syntax_getArgs(v___x_1040_);
lean_dec_ref(v___x_1040_);
v_x_554_ = v_x_976_;
v_ty_555_ = v_ty_1035_;
v_xs_556_ = v_xs_1049_;
v_P_557_ = v_____discr_944_;
v___y_558_ = v___y_945_;
v___y_559_ = v___y_946_;
goto v___jp_553_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = l_Lean_Syntax_matchesNull(v_____discr_943_, v___x_481_);
if (v___x_1050_ == 0)
{
lean_dec(v___x_947_);
lean_dec(v_____discr_944_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v___y_946_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_xs_1056_; 
v___x_1051_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1052_ = l_Array_extract___redArg(v___x_1051_, v___x_482_, v___x_947_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1054_ = lean_box(2);
v___x_1055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
lean_ctor_set(v___x_1055_, 2, v___x_1052_);
v_xs_1056_ = l_Lean_Syntax_getArgs(v___x_1055_);
lean_dec_ref(v___x_1055_);
v_x_498_ = v_x_821_;
v_xs_499_ = v_xs_1056_;
v_P_500_ = v_____discr_944_;
v___y_501_ = v___y_945_;
v___y_502_ = v___y_946_;
goto v___jp_497_;
}
}
}
}
}
else
{
lean_object* v_tk_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_tk_1700_ = l_Lean_Syntax_getArg(v_x_821_, v___x_481_);
v___x_1701_ = lean_unsigned_to_nat(2u);
v___x_1702_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1701_);
lean_inc(v___x_1702_);
v___x_1703_ = l_Lean_Syntax_matchesNull(v___x_1702_, v___x_481_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1704_; 
lean_inc(v___x_1702_);
v___x_1704_ = l_Lean_Syntax_matchesNull(v___x_1702_, v___x_482_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
lean_dec(v___x_1702_);
lean_dec(v_tk_1700_);
v___x_1705_ = l_Lean_Syntax_getNumArgs(v___x_687_);
v___x_1706_ = lean_nat_dec_le(v___x_482_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1707_; lean_object* v_P_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1707_ = lean_unsigned_to_nat(4u);
v_P_1708_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1707_);
lean_dec(v___x_483_);
v___x_1709_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_821_);
v___x_1710_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_821_);
v___x_1712_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1713_ = lean_unsigned_to_nat(3u);
v___x_1714_ = l_Lean_Syntax_getArg(v_x_821_, v___x_482_);
lean_inc(v___x_1714_);
v___x_1715_ = l_Lean_Syntax_matchesNull(v___x_1714_, v___x_482_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = l_Lean_Syntax_getNumArgs(v___x_1714_);
v___x_1717_ = lean_nat_dec_le(v___x_482_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_dec(v___x_1716_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1718_; uint8_t v___x_1719_; 
v_x_1718_ = l_Lean_Syntax_getArg(v___x_1714_, v___x_481_);
lean_inc(v_x_1718_);
v___x_1719_ = l_Lean_Syntax_isOfKind(v_x_1718_, v___x_1709_);
if (v___x_1719_ == 0)
{
lean_dec(v_x_1718_);
lean_dec(v___x_1716_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1701_);
lean_inc(v___x_1720_);
v___x_1721_ = l_Lean_Syntax_matchesNull(v___x_1720_, v___x_1701_);
if (v___x_1721_ == 0)
{
lean_dec(v___x_1720_);
lean_dec(v_x_1718_);
lean_dec(v___x_1716_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1713_);
lean_dec(v_x_821_);
v___x_1723_ = l_Lean_Syntax_matchesNull(v___x_1722_, v___x_481_);
if (v___x_1723_ == 0)
{
lean_dec(v___x_1720_);
lean_dec(v_x_1718_);
lean_dec(v___x_1716_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1720_);
lean_dec(v_x_1718_);
lean_dec(v___x_1716_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_ty_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v_ys_1733_; lean_object* v_xs_1734_; 
v___x_1724_ = l_Lean_Syntax_getArgs(v___x_1714_);
lean_dec(v___x_1714_);
v___x_1725_ = l_Array_extract___redArg(v___x_1724_, v___x_482_, v___x_1716_);
lean_dec_ref(v___x_1724_);
v_ty_1726_ = l_Lean_Syntax_getArg(v___x_1720_, v___x_482_);
lean_dec(v___x_1720_);
v___x_1727_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1728_ = lean_box(2);
v___x_1729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v___x_1727_);
lean_ctor_set(v___x_1729_, 2, v___x_1725_);
v___x_1730_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1731_ = l_Array_extract___redArg(v___x_1730_, v___x_482_, v___x_1705_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1728_);
lean_ctor_set(v___x_1732_, 1, v___x_1727_);
lean_ctor_set(v___x_1732_, 2, v___x_1731_);
v_ys_1733_ = l_Lean_Syntax_getArgs(v___x_1732_);
lean_dec_ref(v___x_1732_);
v_xs_1734_ = l_Lean_Syntax_getArgs(v___x_1729_);
lean_dec_ref(v___x_1729_);
v_x_616_ = v_x_1718_;
v_xs_617_ = v_xs_1734_;
v_ty_618_ = v_ty_1726_;
v_ys_619_ = v_ys_1733_;
v_P_620_ = v_P_1708_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_x_1735_; uint8_t v___x_1736_; 
v_x_1735_ = l_Lean_Syntax_getArg(v___x_1714_, v___x_481_);
lean_inc(v_x_1735_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v_x_1735_, v___x_1709_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = l_Lean_Syntax_getNumArgs(v___x_1714_);
v___x_1738_ = lean_nat_dec_le(v___x_482_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_dec(v___x_1737_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1736_ == 0)
{
lean_dec(v___x_1737_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1701_);
lean_inc(v___x_1739_);
v___x_1740_ = l_Lean_Syntax_matchesNull(v___x_1739_, v___x_1701_);
if (v___x_1740_ == 0)
{
lean_dec(v___x_1739_);
lean_dec(v___x_1737_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1713_);
lean_dec(v_x_821_);
v___x_1742_ = l_Lean_Syntax_matchesNull(v___x_1741_, v___x_481_);
if (v___x_1742_ == 0)
{
lean_dec(v___x_1739_);
lean_dec(v___x_1737_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1739_);
lean_dec(v___x_1737_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_ty_1751_; lean_object* v_ys_1752_; lean_object* v_xs_1753_; 
v___x_1743_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1744_ = l_Array_extract___redArg(v___x_1743_, v___x_482_, v___x_1705_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1746_ = lean_box(2);
v___x_1747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___x_1745_);
lean_ctor_set(v___x_1747_, 2, v___x_1744_);
v___x_1748_ = l_Lean_Syntax_getArgs(v___x_1714_);
lean_dec(v___x_1714_);
v___x_1749_ = l_Array_extract___redArg(v___x_1748_, v___x_482_, v___x_1737_);
lean_dec_ref(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1746_);
lean_ctor_set(v___x_1750_, 1, v___x_1745_);
lean_ctor_set(v___x_1750_, 2, v___x_1749_);
v_ty_1751_ = l_Lean_Syntax_getArg(v___x_1739_, v___x_482_);
lean_dec(v___x_1739_);
v_ys_1752_ = l_Lean_Syntax_getArgs(v___x_1747_);
lean_dec_ref(v___x_1747_);
v_xs_1753_ = l_Lean_Syntax_getArgs(v___x_1750_);
lean_dec_ref(v___x_1750_);
v_x_616_ = v_x_1735_;
v_xs_617_ = v_xs_1753_;
v_ty_618_ = v_ty_1751_;
v_ys_619_ = v_ys_1752_;
v_P_620_ = v_P_1708_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1701_);
lean_inc(v___x_1754_);
v___x_1755_ = l_Lean_Syntax_matchesNull(v___x_1754_, v___x_1701_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = l_Lean_Syntax_getNumArgs(v___x_1714_);
v___x_1757_ = lean_nat_dec_le(v___x_482_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec(v___x_1756_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1736_ == 0)
{
lean_dec(v___x_1756_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1755_ == 0)
{
lean_dec(v___x_1756_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1713_);
lean_dec(v_x_821_);
v___x_1759_ = l_Lean_Syntax_matchesNull(v___x_1758_, v___x_481_);
if (v___x_1759_ == 0)
{
lean_dec(v___x_1756_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1756_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_ty_1768_; lean_object* v_ys_1769_; lean_object* v_xs_1770_; 
v___x_1760_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1761_ = l_Array_extract___redArg(v___x_1760_, v___x_482_, v___x_1705_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1763_ = lean_box(2);
v___x_1764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v___x_1762_);
lean_ctor_set(v___x_1764_, 2, v___x_1761_);
v___x_1765_ = l_Lean_Syntax_getArgs(v___x_1714_);
lean_dec(v___x_1714_);
v___x_1766_ = l_Array_extract___redArg(v___x_1765_, v___x_482_, v___x_1756_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1763_);
lean_ctor_set(v___x_1767_, 1, v___x_1762_);
lean_ctor_set(v___x_1767_, 2, v___x_1766_);
v_ty_1768_ = l_Lean_Syntax_getArg(v___x_1754_, v___x_482_);
lean_dec(v___x_1754_);
v_ys_1769_ = l_Lean_Syntax_getArgs(v___x_1764_);
lean_dec_ref(v___x_1764_);
v_xs_1770_ = l_Lean_Syntax_getArgs(v___x_1767_);
lean_dec_ref(v___x_1767_);
v_x_616_ = v_x_1735_;
v_xs_617_ = v_xs_1770_;
v_ty_618_ = v_ty_1768_;
v_ys_619_ = v_ys_1769_;
v_P_620_ = v_P_1708_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1713_);
lean_dec(v_x_821_);
v___x_1772_ = l_Lean_Syntax_matchesNull(v___x_1771_, v___x_481_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = l_Lean_Syntax_getNumArgs(v___x_1714_);
v___x_1774_ = lean_nat_dec_le(v___x_482_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec(v___x_1773_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1736_ == 0)
{
lean_dec(v___x_1773_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1755_ == 0)
{
lean_dec(v___x_1773_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1772_ == 0)
{
lean_dec(v___x_1773_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1773_);
lean_dec(v___x_1754_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_ty_1783_; lean_object* v_ys_1784_; lean_object* v_xs_1785_; 
v___x_1775_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1776_ = l_Array_extract___redArg(v___x_1775_, v___x_482_, v___x_1705_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1778_ = lean_box(2);
v___x_1779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___x_1777_);
lean_ctor_set(v___x_1779_, 2, v___x_1776_);
v___x_1780_ = l_Lean_Syntax_getArgs(v___x_1714_);
lean_dec(v___x_1714_);
v___x_1781_ = l_Array_extract___redArg(v___x_1780_, v___x_482_, v___x_1773_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1778_);
lean_ctor_set(v___x_1782_, 1, v___x_1777_);
lean_ctor_set(v___x_1782_, 2, v___x_1781_);
v_ty_1783_ = l_Lean_Syntax_getArg(v___x_1754_, v___x_482_);
lean_dec(v___x_1754_);
v_ys_1784_ = l_Lean_Syntax_getArgs(v___x_1779_);
lean_dec_ref(v___x_1779_);
v_xs_1785_ = l_Lean_Syntax_getArgs(v___x_1782_);
lean_dec_ref(v___x_1782_);
v_x_616_ = v_x_1735_;
v_xs_617_ = v_xs_1785_;
v_ty_618_ = v_ty_1783_;
v_ys_619_ = v_ys_1784_;
v_P_620_ = v_P_1708_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_ty_1786_ = l_Lean_Syntax_getArg(v___x_1754_, v___x_482_);
lean_dec(v___x_1754_);
v___x_1787_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1788_ = l_Array_extract___redArg(v___x_1787_, v___x_482_, v___x_1705_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1790_ = lean_box(2);
v___x_1791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1789_);
lean_ctor_set(v___x_1791_, 2, v___x_1788_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = l_Lean_Syntax_getNumArgs(v___x_1714_);
v___x_1793_ = lean_nat_dec_le(v___x_482_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_dec(v___x_1792_);
lean_dec_ref(v___x_1791_);
lean_dec(v_ty_1786_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1736_ == 0)
{
lean_dec(v___x_1792_);
lean_dec_ref(v___x_1791_);
lean_dec(v_ty_1786_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1755_ == 0)
{
lean_dec(v___x_1792_);
lean_dec_ref(v___x_1791_);
lean_dec(v_ty_1786_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1772_ == 0)
{
lean_dec(v___x_1792_);
lean_dec_ref(v___x_1791_);
lean_dec(v_ty_1786_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1792_);
lean_dec_ref(v___x_1791_);
lean_dec(v_ty_1786_);
lean_dec(v_x_1735_);
lean_dec(v___x_1714_);
lean_dec(v_P_1708_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_ys_1797_; lean_object* v_xs_1798_; 
v___x_1794_ = l_Lean_Syntax_getArgs(v___x_1714_);
lean_dec(v___x_1714_);
v___x_1795_ = l_Array_extract___redArg(v___x_1794_, v___x_482_, v___x_1792_);
lean_dec_ref(v___x_1794_);
v___x_1796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1790_);
lean_ctor_set(v___x_1796_, 1, v___x_1789_);
lean_ctor_set(v___x_1796_, 2, v___x_1795_);
v_ys_1797_ = l_Lean_Syntax_getArgs(v___x_1791_);
lean_dec_ref(v___x_1791_);
v_xs_1798_ = l_Lean_Syntax_getArgs(v___x_1796_);
lean_dec_ref(v___x_1796_);
v_x_616_ = v_x_1735_;
v_xs_617_ = v_xs_1798_;
v_ty_618_ = v_ty_1786_;
v_ys_619_ = v_ys_1797_;
v_P_620_ = v_P_1708_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1799_; 
lean_dec(v___x_1714_);
v_xs_1799_ = l_Lean_Syntax_getArgs(v___x_1791_);
lean_dec_ref(v___x_1791_);
v_x_554_ = v_x_1735_;
v_ty_555_ = v_ty_1786_;
v_xs_556_ = v_xs_1799_;
v_P_557_ = v_P_1708_;
v___y_558_ = v_a_471_;
v___y_559_ = v_a_472_;
goto v___jp_553_;
}
}
}
}
}
}
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v_P_1708_);
lean_dec(v___x_1705_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_xs_1805_; 
v___x_1800_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1801_ = l_Array_extract___redArg(v___x_1800_, v___x_482_, v___x_1705_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1803_ = lean_box(2);
v___x_1804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1802_);
lean_ctor_set(v___x_1804_, 2, v___x_1801_);
v_xs_1805_ = l_Lean_Syntax_getArgs(v___x_1804_);
lean_dec_ref(v___x_1804_);
v_x_498_ = v_x_821_;
v_xs_499_ = v_xs_1805_;
v_P_500_ = v_P_1708_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1806_ = l_Lean_Syntax_getArg(v___x_1702_, v___x_481_);
lean_dec(v___x_1702_);
v___x_1807_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
lean_inc(v___x_1806_);
v___x_1808_ = l_Lean_Syntax_isOfKind(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
lean_dec(v___x_1806_);
lean_dec(v_tk_1700_);
v___x_1809_ = l_Lean_Syntax_getNumArgs(v___x_687_);
v___x_1810_ = lean_nat_dec_le(v___x_482_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1811_; lean_object* v_P_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1811_ = lean_unsigned_to_nat(4u);
v_P_1812_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1811_);
lean_dec(v___x_483_);
v___x_1813_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_821_);
v___x_1814_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_821_);
v___x_1816_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1817_ = lean_unsigned_to_nat(3u);
v___x_1818_ = l_Lean_Syntax_getArg(v_x_821_, v___x_482_);
lean_inc(v___x_1818_);
v___x_1819_ = l_Lean_Syntax_matchesNull(v___x_1818_, v___x_482_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = l_Lean_Syntax_getNumArgs(v___x_1818_);
v___x_1821_ = lean_nat_dec_le(v___x_482_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_dec(v___x_1820_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1822_; uint8_t v___x_1823_; 
v_x_1822_ = l_Lean_Syntax_getArg(v___x_1818_, v___x_481_);
lean_inc(v_x_1822_);
v___x_1823_ = l_Lean_Syntax_isOfKind(v_x_1822_, v___x_1813_);
if (v___x_1823_ == 0)
{
lean_dec(v_x_1822_);
lean_dec(v___x_1820_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1701_);
lean_inc(v___x_1824_);
v___x_1825_ = l_Lean_Syntax_matchesNull(v___x_1824_, v___x_1701_);
if (v___x_1825_ == 0)
{
lean_dec(v___x_1824_);
lean_dec(v_x_1822_);
lean_dec(v___x_1820_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1817_);
lean_dec(v_x_821_);
v___x_1827_ = l_Lean_Syntax_matchesNull(v___x_1826_, v___x_481_);
if (v___x_1827_ == 0)
{
lean_dec(v___x_1824_);
lean_dec(v_x_1822_);
lean_dec(v___x_1820_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1824_);
lean_dec(v_x_1822_);
lean_dec(v___x_1820_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v_ty_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_ys_1837_; lean_object* v_xs_1838_; 
v___x_1828_ = l_Lean_Syntax_getArgs(v___x_1818_);
lean_dec(v___x_1818_);
v___x_1829_ = l_Array_extract___redArg(v___x_1828_, v___x_482_, v___x_1820_);
lean_dec_ref(v___x_1828_);
v_ty_1830_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_482_);
lean_dec(v___x_1824_);
v___x_1831_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1832_ = lean_box(2);
v___x_1833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___x_1831_);
lean_ctor_set(v___x_1833_, 2, v___x_1829_);
v___x_1834_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1835_ = l_Array_extract___redArg(v___x_1834_, v___x_482_, v___x_1809_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1832_);
lean_ctor_set(v___x_1836_, 1, v___x_1831_);
lean_ctor_set(v___x_1836_, 2, v___x_1835_);
v_ys_1837_ = l_Lean_Syntax_getArgs(v___x_1836_);
lean_dec_ref(v___x_1836_);
v_xs_1838_ = l_Lean_Syntax_getArgs(v___x_1833_);
lean_dec_ref(v___x_1833_);
v_x_616_ = v_x_1822_;
v_xs_617_ = v_xs_1838_;
v_ty_618_ = v_ty_1830_;
v_ys_619_ = v_ys_1837_;
v_P_620_ = v_P_1812_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_x_1839_; uint8_t v___x_1840_; 
v_x_1839_ = l_Lean_Syntax_getArg(v___x_1818_, v___x_481_);
lean_inc(v_x_1839_);
v___x_1840_ = l_Lean_Syntax_isOfKind(v_x_1839_, v___x_1813_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = l_Lean_Syntax_getNumArgs(v___x_1818_);
v___x_1842_ = lean_nat_dec_le(v___x_482_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec(v___x_1841_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1840_ == 0)
{
lean_dec(v___x_1841_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1701_);
lean_inc(v___x_1843_);
v___x_1844_ = l_Lean_Syntax_matchesNull(v___x_1843_, v___x_1701_);
if (v___x_1844_ == 0)
{
lean_dec(v___x_1843_);
lean_dec(v___x_1841_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1817_);
lean_dec(v_x_821_);
v___x_1846_ = l_Lean_Syntax_matchesNull(v___x_1845_, v___x_481_);
if (v___x_1846_ == 0)
{
lean_dec(v___x_1843_);
lean_dec(v___x_1841_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1843_);
lean_dec(v___x_1841_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v_ty_1855_; lean_object* v_ys_1856_; lean_object* v_xs_1857_; 
v___x_1847_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1848_ = l_Array_extract___redArg(v___x_1847_, v___x_482_, v___x_1809_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1850_ = lean_box(2);
v___x_1851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1849_);
lean_ctor_set(v___x_1851_, 2, v___x_1848_);
v___x_1852_ = l_Lean_Syntax_getArgs(v___x_1818_);
lean_dec(v___x_1818_);
v___x_1853_ = l_Array_extract___redArg(v___x_1852_, v___x_482_, v___x_1841_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1850_);
lean_ctor_set(v___x_1854_, 1, v___x_1849_);
lean_ctor_set(v___x_1854_, 2, v___x_1853_);
v_ty_1855_ = l_Lean_Syntax_getArg(v___x_1843_, v___x_482_);
lean_dec(v___x_1843_);
v_ys_1856_ = l_Lean_Syntax_getArgs(v___x_1851_);
lean_dec_ref(v___x_1851_);
v_xs_1857_ = l_Lean_Syntax_getArgs(v___x_1854_);
lean_dec_ref(v___x_1854_);
v_x_616_ = v_x_1839_;
v_xs_617_ = v_xs_1857_;
v_ty_618_ = v_ty_1855_;
v_ys_619_ = v_ys_1856_;
v_P_620_ = v_P_1812_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1701_);
lean_inc(v___x_1858_);
v___x_1859_ = l_Lean_Syntax_matchesNull(v___x_1858_, v___x_1701_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = l_Lean_Syntax_getNumArgs(v___x_1818_);
v___x_1861_ = lean_nat_dec_le(v___x_482_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_dec(v___x_1860_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1840_ == 0)
{
lean_dec(v___x_1860_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1859_ == 0)
{
lean_dec(v___x_1860_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1817_);
lean_dec(v_x_821_);
v___x_1863_ = l_Lean_Syntax_matchesNull(v___x_1862_, v___x_481_);
if (v___x_1863_ == 0)
{
lean_dec(v___x_1860_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1860_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_ty_1872_; lean_object* v_ys_1873_; lean_object* v_xs_1874_; 
v___x_1864_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1865_ = l_Array_extract___redArg(v___x_1864_, v___x_482_, v___x_1809_);
lean_dec_ref(v___x_1864_);
v___x_1866_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1867_ = lean_box(2);
v___x_1868_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1866_);
lean_ctor_set(v___x_1868_, 2, v___x_1865_);
v___x_1869_ = l_Lean_Syntax_getArgs(v___x_1818_);
lean_dec(v___x_1818_);
v___x_1870_ = l_Array_extract___redArg(v___x_1869_, v___x_482_, v___x_1860_);
lean_dec_ref(v___x_1869_);
v___x_1871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1867_);
lean_ctor_set(v___x_1871_, 1, v___x_1866_);
lean_ctor_set(v___x_1871_, 2, v___x_1870_);
v_ty_1872_ = l_Lean_Syntax_getArg(v___x_1858_, v___x_482_);
lean_dec(v___x_1858_);
v_ys_1873_ = l_Lean_Syntax_getArgs(v___x_1868_);
lean_dec_ref(v___x_1868_);
v_xs_1874_ = l_Lean_Syntax_getArgs(v___x_1871_);
lean_dec_ref(v___x_1871_);
v_x_616_ = v_x_1839_;
v_xs_617_ = v_xs_1874_;
v_ty_618_ = v_ty_1872_;
v_ys_619_ = v_ys_1873_;
v_P_620_ = v_P_1812_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = l_Lean_Syntax_getArg(v_x_821_, v___x_1817_);
lean_dec(v_x_821_);
v___x_1876_ = l_Lean_Syntax_matchesNull(v___x_1875_, v___x_481_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = l_Lean_Syntax_getNumArgs(v___x_1818_);
v___x_1878_ = lean_nat_dec_le(v___x_482_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_dec(v___x_1877_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1840_ == 0)
{
lean_dec(v___x_1877_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1859_ == 0)
{
lean_dec(v___x_1877_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1876_ == 0)
{
lean_dec(v___x_1877_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1877_);
lean_dec(v___x_1858_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v_ty_1887_; lean_object* v_ys_1888_; lean_object* v_xs_1889_; 
v___x_1879_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1880_ = l_Array_extract___redArg(v___x_1879_, v___x_482_, v___x_1809_);
lean_dec_ref(v___x_1879_);
v___x_1881_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1882_ = lean_box(2);
v___x_1883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1881_);
lean_ctor_set(v___x_1883_, 2, v___x_1880_);
v___x_1884_ = l_Lean_Syntax_getArgs(v___x_1818_);
lean_dec(v___x_1818_);
v___x_1885_ = l_Array_extract___redArg(v___x_1884_, v___x_482_, v___x_1877_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1882_);
lean_ctor_set(v___x_1886_, 1, v___x_1881_);
lean_ctor_set(v___x_1886_, 2, v___x_1885_);
v_ty_1887_ = l_Lean_Syntax_getArg(v___x_1858_, v___x_482_);
lean_dec(v___x_1858_);
v_ys_1888_ = l_Lean_Syntax_getArgs(v___x_1883_);
lean_dec_ref(v___x_1883_);
v_xs_1889_ = l_Lean_Syntax_getArgs(v___x_1886_);
lean_dec_ref(v___x_1886_);
v_x_616_ = v_x_1839_;
v_xs_617_ = v_xs_1889_;
v_ty_618_ = v_ty_1887_;
v_ys_619_ = v_ys_1888_;
v_P_620_ = v_P_1812_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_ty_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_ty_1890_ = l_Lean_Syntax_getArg(v___x_1858_, v___x_482_);
lean_dec(v___x_1858_);
v___x_1891_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1892_ = l_Array_extract___redArg(v___x_1891_, v___x_482_, v___x_1809_);
lean_dec_ref(v___x_1891_);
v___x_1893_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1894_ = lean_box(2);
v___x_1895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___x_1893_);
lean_ctor_set(v___x_1895_, 2, v___x_1892_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = l_Lean_Syntax_getNumArgs(v___x_1818_);
v___x_1897_ = lean_nat_dec_le(v___x_482_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_dec(v___x_1896_);
lean_dec_ref(v___x_1895_);
lean_dec(v_ty_1890_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1840_ == 0)
{
lean_dec(v___x_1896_);
lean_dec_ref(v___x_1895_);
lean_dec(v_ty_1890_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1859_ == 0)
{
lean_dec(v___x_1896_);
lean_dec_ref(v___x_1895_);
lean_dec(v_ty_1890_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1876_ == 0)
{
lean_dec(v___x_1896_);
lean_dec_ref(v___x_1895_);
lean_dec(v_ty_1890_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v___x_1896_);
lean_dec_ref(v___x_1895_);
lean_dec(v_ty_1890_);
lean_dec(v_x_1839_);
lean_dec(v___x_1818_);
lean_dec(v_P_1812_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_ys_1901_; lean_object* v_xs_1902_; 
v___x_1898_ = l_Lean_Syntax_getArgs(v___x_1818_);
lean_dec(v___x_1818_);
v___x_1899_ = l_Array_extract___redArg(v___x_1898_, v___x_482_, v___x_1896_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1894_);
lean_ctor_set(v___x_1900_, 1, v___x_1893_);
lean_ctor_set(v___x_1900_, 2, v___x_1899_);
v_ys_1901_ = l_Lean_Syntax_getArgs(v___x_1895_);
lean_dec_ref(v___x_1895_);
v_xs_1902_ = l_Lean_Syntax_getArgs(v___x_1900_);
lean_dec_ref(v___x_1900_);
v_x_616_ = v_x_1839_;
v_xs_617_ = v_xs_1902_;
v_ty_618_ = v_ty_1890_;
v_ys_619_ = v_ys_1901_;
v_P_620_ = v_P_1812_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_xs_1903_; 
lean_dec(v___x_1818_);
v_xs_1903_ = l_Lean_Syntax_getArgs(v___x_1895_);
lean_dec_ref(v___x_1895_);
v_x_554_ = v_x_1839_;
v_ty_555_ = v_ty_1890_;
v_xs_556_ = v_xs_1903_;
v_P_557_ = v_P_1812_;
v___y_558_ = v_a_471_;
v___y_559_ = v_a_472_;
goto v___jp_553_;
}
}
}
}
}
}
}
else
{
if (v___x_1703_ == 0)
{
lean_dec(v_P_1812_);
lean_dec(v___x_1809_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_xs_1909_; 
v___x_1904_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_1905_ = l_Array_extract___redArg(v___x_1904_, v___x_482_, v___x_1809_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1907_ = lean_box(2);
v___x_1908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1906_);
lean_ctor_set(v___x_1908_, 2, v___x_1905_);
v_xs_1909_ = l_Lean_Syntax_getArgs(v___x_1908_);
lean_dec_ref(v___x_1908_);
v_x_498_ = v_x_821_;
v_xs_499_ = v_xs_1909_;
v_P_500_ = v_P_1812_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v_quotContext_1910_; lean_object* v_currMacroScope_1911_; lean_object* v_ref_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_quotContext_1910_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1911_ = lean_ctor_get(v_a_471_, 2);
v_ref_1912_ = lean_ctor_get(v_a_471_, 5);
v___x_1913_ = l_Lean_Syntax_getArg(v___x_1806_, v___x_482_);
lean_dec(v___x_1806_);
v___x_1914_ = lean_unsigned_to_nat(4u);
v___x_1915_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1914_);
lean_dec(v___x_483_);
v___x_1916_ = l_Lean_SourceInfo_fromRef(v_ref_1912_, v___x_1703_);
v___x_1917_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1918_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1919_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1911_, 2);
lean_inc_n(v_quotContext_1910_, 2);
v___x_1920_ = l_Lean_addMacroScope(v_quotContext_1910_, v___x_1919_, v_currMacroScope_1911_);
v___x_1921_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1916_, 19);
v___x_1922_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1916_);
lean_ctor_set(v___x_1922_, 1, v___x_1918_);
lean_ctor_set(v___x_1922_, 2, v___x_1920_);
lean_ctor_set(v___x_1922_, 3, v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1924_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1925_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1926_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1916_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1929_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1930_ = lean_box(0);
v___x_1931_ = l_Lean_addMacroScope(v_quotContext_1910_, v___x_1930_, v_currMacroScope_1911_);
v___x_1932_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1933_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1916_);
lean_ctor_set(v___x_1933_, 1, v___x_1929_);
lean_ctor_set(v___x_1933_, 2, v___x_1931_);
lean_ctor_set(v___x_1933_, 3, v___x_1932_);
v___x_1934_ = l_Lean_Syntax_node1(v___x_1916_, v___x_1928_, v___x_1933_);
v___x_1935_ = l_Lean_Syntax_node2(v___x_1916_, v___x_1925_, v___x_1927_, v___x_1934_);
v___x_1936_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1937_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1916_);
lean_ctor_set(v___x_1938_, 1, v___x_1936_);
v___x_1939_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1940_ = l_Lean_SourceInfo_fromRef(v_tk_1700_, v___x_688_);
lean_dec(v_tk_1700_);
v___x_1941_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_Syntax_node1(v___x_1916_, v___x_822_, v___x_1942_);
v___x_1944_ = l_Lean_Syntax_node1(v___x_1916_, v___x_1923_, v___x_1943_);
v___x_1945_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1916_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_Syntax_node2(v___x_1916_, v___x_1807_, v___x_1946_, v___x_1913_);
v___x_1948_ = l_Lean_Syntax_node1(v___x_1916_, v___x_1923_, v___x_1947_);
v___x_1949_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1916_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1916_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1916_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
lean_inc_ref(v___x_1954_);
v___x_1955_ = l_Lean_Syntax_node3(v___x_1916_, v___x_477_, v___x_1952_, v___x_1915_, v___x_1954_);
v___x_1956_ = l_Lean_Syntax_node4(v___x_1916_, v___x_1939_, v___x_1944_, v___x_1948_, v___x_1950_, v___x_1955_);
v___x_1957_ = l_Lean_Syntax_node2(v___x_1916_, v___x_1937_, v___x_1938_, v___x_1956_);
v___x_1958_ = l_Lean_Syntax_node3(v___x_1916_, v___x_1924_, v___x_1935_, v___x_1957_, v___x_1954_);
v___x_1959_ = l_Lean_Syntax_node1(v___x_1916_, v___x_1923_, v___x_1958_);
v___x_1960_ = l_Lean_Syntax_node2(v___x_1916_, v___x_1917_, v___x_1922_, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v_a_472_);
return v___x_1961_;
}
}
}
else
{
lean_object* v_quotContext_1962_; lean_object* v_currMacroScope_1963_; lean_object* v_ref_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v___x_1702_);
lean_dec(v_x_821_);
lean_dec(v___x_687_);
v_quotContext_1962_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1963_ = lean_ctor_get(v_a_471_, 2);
v_ref_1964_ = lean_ctor_get(v_a_471_, 5);
v___x_1965_ = lean_unsigned_to_nat(4u);
v___x_1966_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1965_);
lean_dec(v___x_483_);
v___x_1967_ = l_Lean_SourceInfo_fromRef(v_ref_1964_, v___x_495_);
v___x_1968_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1969_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1970_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1963_, 2);
lean_inc_n(v_quotContext_1962_, 2);
v___x_1971_ = l_Lean_addMacroScope(v_quotContext_1962_, v___x_1970_, v_currMacroScope_1963_);
v___x_1972_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1967_, 17);
v___x_1973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1967_);
lean_ctor_set(v___x_1973_, 1, v___x_1969_);
lean_ctor_set(v___x_1973_, 2, v___x_1971_);
lean_ctor_set(v___x_1973_, 3, v___x_1972_);
v___x_1974_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1975_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1976_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1977_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1967_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1980_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1981_ = lean_box(0);
v___x_1982_ = l_Lean_addMacroScope(v_quotContext_1962_, v___x_1981_, v_currMacroScope_1963_);
v___x_1983_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1967_);
lean_ctor_set(v___x_1984_, 1, v___x_1980_);
lean_ctor_set(v___x_1984_, 2, v___x_1982_);
lean_ctor_set(v___x_1984_, 3, v___x_1983_);
v___x_1985_ = l_Lean_Syntax_node1(v___x_1967_, v___x_1979_, v___x_1984_);
v___x_1986_ = l_Lean_Syntax_node2(v___x_1967_, v___x_1976_, v___x_1978_, v___x_1985_);
v___x_1987_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1988_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1967_);
lean_ctor_set(v___x_1989_, 1, v___x_1987_);
v___x_1990_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1991_ = l_Lean_SourceInfo_fromRef(v_tk_1700_, v___x_688_);
lean_dec(v_tk_1700_);
v___x_1992_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_Syntax_node1(v___x_1967_, v___x_822_, v___x_1993_);
v___x_1995_ = l_Lean_Syntax_node1(v___x_1967_, v___x_1974_, v___x_1994_);
v___x_1996_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1967_);
lean_ctor_set(v___x_1997_, 1, v___x_1974_);
lean_ctor_set(v___x_1997_, 2, v___x_1996_);
v___x_1998_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1967_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1967_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1967_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
lean_inc_ref(v___x_2003_);
v___x_2004_ = l_Lean_Syntax_node3(v___x_1967_, v___x_477_, v___x_2001_, v___x_1966_, v___x_2003_);
v___x_2005_ = l_Lean_Syntax_node4(v___x_1967_, v___x_1990_, v___x_1995_, v___x_1997_, v___x_1999_, v___x_2004_);
v___x_2006_ = l_Lean_Syntax_node2(v___x_1967_, v___x_1988_, v___x_1989_, v___x_2005_);
v___x_2007_ = l_Lean_Syntax_node3(v___x_1967_, v___x_1975_, v___x_1986_, v___x_2006_, v___x_2003_);
v___x_2008_ = l_Lean_Syntax_node1(v___x_1967_, v___x_1974_, v___x_2007_);
v___x_2009_ = l_Lean_Syntax_node2(v___x_1967_, v___x_1968_, v___x_1973_, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v_a_472_);
return v___x_2010_;
}
}
v___jp_824_:
{
lean_object* v_quotContext_830_; lean_object* v_currMacroScope_831_; lean_object* v_ref_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_quotContext_830_ = lean_ctor_get(v___y_828_, 1);
v_currMacroScope_831_ = lean_ctor_get(v___y_828_, 2);
v_ref_832_ = lean_ctor_get(v___y_828_, 5);
v___x_833_ = l_Lean_SourceInfo_fromRef(v_ref_832_, v___x_823_);
v___x_834_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_835_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_836_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_831_, 2);
lean_inc_n(v_quotContext_830_, 2);
v___x_837_ = l_Lean_addMacroScope(v_quotContext_830_, v___x_836_, v_currMacroScope_831_);
v___x_838_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_833_, 18);
v___x_839_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_839_, 0, v___x_833_);
lean_ctor_set(v___x_839_, 1, v___x_835_);
lean_ctor_set(v___x_839_, 2, v___x_837_);
lean_ctor_set(v___x_839_, 3, v___x_838_);
v___x_840_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_841_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_842_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_843_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_833_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_846_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_847_ = lean_box(0);
v___x_848_ = l_Lean_addMacroScope(v_quotContext_830_, v___x_847_, v_currMacroScope_831_);
v___x_849_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_850_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_850_, 0, v___x_833_);
lean_ctor_set(v___x_850_, 1, v___x_846_);
lean_ctor_set(v___x_850_, 2, v___x_848_);
lean_ctor_set(v___x_850_, 3, v___x_849_);
v___x_851_ = l_Lean_Syntax_node1(v___x_833_, v___x_845_, v___x_850_);
v___x_852_ = l_Lean_Syntax_node2(v___x_833_, v___x_842_, v___x_844_, v___x_851_);
v___x_853_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_854_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_833_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
v___x_856_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_857_ = l_Lean_Syntax_node1(v___x_833_, v___x_840_, v_x_825_);
v___x_858_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_859_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_833_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_Syntax_node2(v___x_833_, v___x_858_, v___x_860_, v_ty_826_);
v___x_862_ = l_Lean_Syntax_node1(v___x_833_, v___x_840_, v___x_861_);
v___x_863_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_833_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_833_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_833_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
lean_inc_ref(v___x_868_);
v___x_869_ = l_Lean_Syntax_node3(v___x_833_, v___x_477_, v___x_866_, v_P_827_, v___x_868_);
v___x_870_ = l_Lean_Syntax_node4(v___x_833_, v___x_856_, v___x_857_, v___x_862_, v___x_864_, v___x_869_);
v___x_871_ = l_Lean_Syntax_node2(v___x_833_, v___x_854_, v___x_855_, v___x_870_);
v___x_872_ = l_Lean_Syntax_node3(v___x_833_, v___x_841_, v___x_852_, v___x_871_, v___x_868_);
v___x_873_ = l_Lean_Syntax_node1(v___x_833_, v___x_840_, v___x_872_);
v___x_874_ = l_Lean_Syntax_node2(v___x_833_, v___x_834_, v___x_839_, v___x_873_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___y_829_);
return v___x_875_;
}
}
}
v___jp_497_:
{
lean_object* v_quotContext_503_; lean_object* v_currMacroScope_504_; lean_object* v_ref_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_quotContext_503_ = lean_ctor_get(v___y_501_, 1);
v_currMacroScope_504_ = lean_ctor_get(v___y_501_, 2);
v_ref_505_ = lean_ctor_get(v___y_501_, 5);
v___x_506_ = l_Lean_SourceInfo_fromRef(v_ref_505_, v___x_495_);
v___x_507_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_508_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_509_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_504_, 2);
lean_inc_n(v_quotContext_503_, 2);
v___x_510_ = l_Lean_addMacroScope(v_quotContext_503_, v___x_509_, v_currMacroScope_504_);
v___x_511_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_506_, 20);
v___x_512_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_512_, 0, v___x_506_);
lean_ctor_set(v___x_512_, 1, v___x_508_);
lean_ctor_set(v___x_512_, 2, v___x_510_);
lean_ctor_set(v___x_512_, 3, v___x_511_);
v___x_513_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_514_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_515_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_516_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_506_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_519_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_520_ = lean_box(0);
v___x_521_ = l_Lean_addMacroScope(v_quotContext_503_, v___x_520_, v_currMacroScope_504_);
v___x_522_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_523_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_523_, 0, v___x_506_);
lean_ctor_set(v___x_523_, 1, v___x_519_);
lean_ctor_set(v___x_523_, 2, v___x_521_);
lean_ctor_set(v___x_523_, 3, v___x_522_);
v___x_524_ = l_Lean_Syntax_node1(v___x_506_, v___x_518_, v___x_523_);
v___x_525_ = l_Lean_Syntax_node2(v___x_506_, v___x_515_, v___x_517_, v___x_524_);
v___x_526_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_527_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_506_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
v___x_529_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_530_ = l_Lean_Syntax_node1(v___x_506_, v___x_513_, v_x_498_);
v___x_531_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_532_, 0, v___x_506_);
lean_ctor_set(v___x_532_, 1, v___x_513_);
lean_ctor_set(v___x_532_, 2, v___x_531_);
v___x_533_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_506_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_506_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_506_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Array_append___redArg(v___x_531_, v_xs_499_);
lean_dec_ref(v_xs_499_);
v___x_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_540_, 0, v___x_506_);
lean_ctor_set(v___x_540_, 1, v___x_513_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
v___x_541_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_506_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
lean_inc_ref(v___x_532_);
v___x_543_ = l_Lean_Syntax_node5(v___x_506_, v___x_496_, v___x_538_, v___x_540_, v___x_532_, v___x_542_, v_P_500_);
v___x_544_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_506_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
lean_inc_ref(v___x_545_);
v___x_546_ = l_Lean_Syntax_node3(v___x_506_, v___x_477_, v___x_536_, v___x_543_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node4(v___x_506_, v___x_529_, v___x_530_, v___x_532_, v___x_534_, v___x_546_);
v___x_548_ = l_Lean_Syntax_node2(v___x_506_, v___x_527_, v___x_528_, v___x_547_);
v___x_549_ = l_Lean_Syntax_node3(v___x_506_, v___x_514_, v___x_525_, v___x_548_, v___x_545_);
v___x_550_ = l_Lean_Syntax_node1(v___x_506_, v___x_513_, v___x_549_);
v___x_551_ = l_Lean_Syntax_node2(v___x_506_, v___x_507_, v___x_512_, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___y_502_);
return v___x_552_;
}
v___jp_553_:
{
lean_object* v_quotContext_560_; lean_object* v_currMacroScope_561_; lean_object* v_ref_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_quotContext_560_ = lean_ctor_get(v___y_558_, 1);
v_currMacroScope_561_ = lean_ctor_get(v___y_558_, 2);
v_ref_562_ = lean_ctor_get(v___y_558_, 5);
v___x_563_ = l_Lean_SourceInfo_fromRef(v_ref_562_, v___x_495_);
v___x_564_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_565_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_566_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_561_, 2);
lean_inc_n(v_quotContext_560_, 2);
v___x_567_ = l_Lean_addMacroScope(v_quotContext_560_, v___x_566_, v_currMacroScope_561_);
v___x_568_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_563_, 23);
v___x_569_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_569_, 0, v___x_563_);
lean_ctor_set(v___x_569_, 1, v___x_565_);
lean_ctor_set(v___x_569_, 2, v___x_567_);
lean_ctor_set(v___x_569_, 3, v___x_568_);
v___x_570_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_571_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_572_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_573_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_563_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_576_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_577_ = lean_box(0);
v___x_578_ = l_Lean_addMacroScope(v_quotContext_560_, v___x_577_, v_currMacroScope_561_);
v___x_579_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_580_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_580_, 0, v___x_563_);
lean_ctor_set(v___x_580_, 1, v___x_576_);
lean_ctor_set(v___x_580_, 2, v___x_578_);
lean_ctor_set(v___x_580_, 3, v___x_579_);
v___x_581_ = l_Lean_Syntax_node1(v___x_563_, v___x_575_, v___x_580_);
v___x_582_ = l_Lean_Syntax_node2(v___x_563_, v___x_572_, v___x_574_, v___x_581_);
v___x_583_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_584_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_563_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
v___x_586_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_587_ = l_Lean_Syntax_node1(v___x_563_, v___x_570_, v_x_554_);
v___x_588_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_589_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_563_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_Syntax_node2(v___x_563_, v___x_588_, v___x_590_, v_ty_555_);
v___x_592_ = l_Lean_Syntax_node1(v___x_563_, v___x_570_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_563_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_563_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_563_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_600_ = l_Array_append___redArg(v___x_599_, v_xs_556_);
lean_dec_ref(v_xs_556_);
v___x_601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_601_, 0, v___x_563_);
lean_ctor_set(v___x_601_, 1, v___x_570_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v___x_563_);
lean_ctor_set(v___x_602_, 1, v___x_570_);
lean_ctor_set(v___x_602_, 2, v___x_599_);
v___x_603_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_563_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l_Lean_Syntax_node5(v___x_563_, v___x_496_, v___x_598_, v___x_601_, v___x_602_, v___x_604_, v_P_557_);
v___x_606_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_563_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_inc_ref(v___x_607_);
v___x_608_ = l_Lean_Syntax_node3(v___x_563_, v___x_477_, v___x_596_, v___x_605_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node4(v___x_563_, v___x_586_, v___x_587_, v___x_592_, v___x_594_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node2(v___x_563_, v___x_584_, v___x_585_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node3(v___x_563_, v___x_571_, v___x_582_, v___x_610_, v___x_607_);
v___x_612_ = l_Lean_Syntax_node1(v___x_563_, v___x_570_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node2(v___x_563_, v___x_564_, v___x_569_, v___x_612_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___y_559_);
return v___x_614_;
}
v___jp_615_:
{
lean_object* v_quotContext_623_; lean_object* v_currMacroScope_624_; lean_object* v_ref_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_quotContext_623_ = lean_ctor_get(v___y_621_, 1);
v_currMacroScope_624_ = lean_ctor_get(v___y_621_, 2);
v_ref_625_ = lean_ctor_get(v___y_621_, 5);
v___x_626_ = l_Lean_SourceInfo_fromRef(v_ref_625_, v___x_495_);
v___x_627_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_628_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_629_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_624_, 2);
lean_inc_n(v_quotContext_623_, 2);
v___x_630_ = l_Lean_addMacroScope(v_quotContext_623_, v___x_629_, v_currMacroScope_624_);
v___x_631_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_626_, 26);
v___x_632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_632_, 0, v___x_626_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_630_);
lean_ctor_set(v___x_632_, 3, v___x_631_);
v___x_633_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_634_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_635_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_636_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_626_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_639_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_640_ = lean_box(0);
v___x_641_ = l_Lean_addMacroScope(v_quotContext_623_, v___x_640_, v_currMacroScope_624_);
v___x_642_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_643_, 0, v___x_626_);
lean_ctor_set(v___x_643_, 1, v___x_639_);
lean_ctor_set(v___x_643_, 2, v___x_641_);
lean_ctor_set(v___x_643_, 3, v___x_642_);
v___x_644_ = l_Lean_Syntax_node1(v___x_626_, v___x_638_, v___x_643_);
lean_inc_ref(v___x_637_);
v___x_645_ = l_Lean_Syntax_node2(v___x_626_, v___x_635_, v___x_637_, v___x_644_);
v___x_646_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_647_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_626_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
v___x_649_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_650_ = l_Lean_Syntax_node1(v___x_626_, v___x_633_, v_x_616_);
v___x_651_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_652_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_626_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
lean_inc(v_ty_618_);
lean_inc_ref(v___x_653_);
v___x_654_ = l_Lean_Syntax_node2(v___x_626_, v___x_651_, v___x_653_, v_ty_618_);
v___x_655_ = l_Lean_Syntax_node1(v___x_626_, v___x_633_, v___x_654_);
v___x_656_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_626_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_626_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_626_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
v___x_663_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_664_ = l_Array_append___redArg(v___x_663_, v_xs_617_);
lean_dec_ref(v_xs_617_);
v___x_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_626_);
lean_ctor_set(v___x_665_, 1, v___x_633_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
v___x_666_ = l_Lean_Syntax_node2(v___x_626_, v___x_633_, v___x_653_, v_ty_618_);
v___x_667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_667_, 0, v___x_626_);
lean_ctor_set(v___x_667_, 1, v___x_633_);
lean_ctor_set(v___x_667_, 2, v___x_663_);
v___x_668_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_626_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_inc_ref_n(v___x_669_, 2);
lean_inc_ref(v___x_667_);
v___x_670_ = l_Lean_Syntax_node5(v___x_626_, v___x_662_, v___x_637_, v___x_665_, v___x_666_, v___x_667_, v___x_669_);
v___x_671_ = l_Array_mkArray1___redArg(v___x_670_);
v___x_672_ = l_Array_append___redArg(v___x_671_, v_ys_619_);
lean_dec_ref(v_ys_619_);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_626_);
lean_ctor_set(v___x_673_, 1, v___x_633_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
v___x_674_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_626_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_Syntax_node5(v___x_626_, v___x_496_, v___x_661_, v___x_673_, v___x_667_, v___x_675_, v_P_620_);
v___x_677_ = l_Lean_Syntax_node3(v___x_626_, v___x_477_, v___x_659_, v___x_676_, v___x_669_);
v___x_678_ = l_Lean_Syntax_node4(v___x_626_, v___x_649_, v___x_650_, v___x_655_, v___x_657_, v___x_677_);
v___x_679_ = l_Lean_Syntax_node2(v___x_626_, v___x_647_, v___x_648_, v___x_678_);
v___x_680_ = l_Lean_Syntax_node3(v___x_626_, v___x_634_, v___x_645_, v___x_679_, v___x_669_);
v___x_681_ = l_Lean_Syntax_node1(v___x_626_, v___x_633_, v___x_680_);
v___x_682_ = l_Lean_Syntax_node2(v___x_626_, v___x_627_, v___x_632_, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___y_622_);
return v___x_683_;
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
v___x_2012_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
lean_inc(v___x_2011_);
v___x_2013_ = l_Lean_Syntax_isOfKind(v___x_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v___x_2011_);
lean_dec(v___x_483_);
v___x_2014_ = lean_box(1);
v___x_2015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v_a_472_);
return v___x_2015_;
}
else
{
lean_object* v_ref_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_ref_2016_ = lean_ctor_get(v_a_471_, 5);
v___x_2017_ = lean_unsigned_to_nat(3u);
v___x_2018_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2017_);
lean_dec(v___x_483_);
v___x_2019_ = l_Lean_SourceInfo_fromRef(v_ref_2016_, v___x_493_);
v___x_2020_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2019_, 2);
v___x_2021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2019_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_Syntax_node3(v___x_2019_, v___x_477_, v___x_2021_, v___x_2018_, v___x_2023_);
v___x_2025_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67));
v___x_2026_ = l_Lean_expandExplicitBinders(v___x_2025_, v___x_2011_, v___x_2024_, v_a_471_, v_a_472_);
lean_dec(v___x_2011_);
return v___x_2026_;
}
}
}
else
{
lean_object* v_quotContext_2027_; lean_object* v_currMacroScope_2028_; lean_object* v_ref_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_quotContext_2027_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2028_ = lean_ctor_get(v_a_471_, 2);
v_ref_2029_ = lean_ctor_get(v_a_471_, 5);
v___x_2030_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2031_ = lean_unsigned_to_nat(2u);
v___x_2032_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2031_);
lean_dec(v___x_483_);
v___x_2033_ = l_Lean_SourceInfo_fromRef(v_ref_2029_, v___x_491_);
v___x_2034_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2035_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69);
v___x_2036_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71));
lean_inc(v_currMacroScope_2028_);
lean_inc(v_quotContext_2027_);
v___x_2037_ = l_Lean_addMacroScope(v_quotContext_2027_, v___x_2036_, v_currMacroScope_2028_);
v___x_2038_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__74));
lean_inc_n(v___x_2033_, 6);
v___x_2039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2033_);
lean_ctor_set(v___x_2039_, 1, v___x_2035_);
lean_ctor_set(v___x_2039_, 2, v___x_2037_);
lean_ctor_set(v___x_2039_, 3, v___x_2038_);
v___x_2040_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2041_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2033_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2033_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
lean_inc_ref(v___x_2044_);
lean_inc_ref(v___x_2042_);
v___x_2045_ = l_Lean_Syntax_node3(v___x_2033_, v___x_477_, v___x_2042_, v___x_2030_, v___x_2044_);
v___x_2046_ = l_Lean_Syntax_node3(v___x_2033_, v___x_477_, v___x_2042_, v___x_2032_, v___x_2044_);
v___x_2047_ = l_Lean_Syntax_node2(v___x_2033_, v___x_2040_, v___x_2045_, v___x_2046_);
v___x_2048_ = l_Lean_Syntax_node2(v___x_2033_, v___x_2034_, v___x_2039_, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v_a_472_);
return v___x_2049_;
}
}
else
{
lean_object* v_quotContext_2050_; lean_object* v_currMacroScope_2051_; lean_object* v_ref_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_quotContext_2050_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2051_ = lean_ctor_get(v_a_471_, 2);
v_ref_2052_ = lean_ctor_get(v_a_471_, 5);
v___x_2053_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2054_ = lean_unsigned_to_nat(2u);
v___x_2055_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2054_);
lean_dec(v___x_483_);
v___x_2056_ = l_Lean_SourceInfo_fromRef(v_ref_2052_, v___x_489_);
v___x_2057_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2058_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76);
v___x_2059_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78));
lean_inc(v_currMacroScope_2051_);
lean_inc(v_quotContext_2050_);
v___x_2060_ = l_Lean_addMacroScope(v_quotContext_2050_, v___x_2059_, v_currMacroScope_2051_);
v___x_2061_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__81));
lean_inc_n(v___x_2056_, 6);
v___x_2062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2056_);
lean_ctor_set(v___x_2062_, 1, v___x_2058_);
lean_ctor_set(v___x_2062_, 2, v___x_2060_);
lean_ctor_set(v___x_2062_, 3, v___x_2061_);
v___x_2063_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2064_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2056_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2056_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
lean_inc_ref(v___x_2067_);
lean_inc_ref(v___x_2065_);
v___x_2068_ = l_Lean_Syntax_node3(v___x_2056_, v___x_477_, v___x_2065_, v___x_2053_, v___x_2067_);
v___x_2069_ = l_Lean_Syntax_node3(v___x_2056_, v___x_477_, v___x_2065_, v___x_2055_, v___x_2067_);
v___x_2070_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2063_, v___x_2068_, v___x_2069_);
v___x_2071_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2057_, v___x_2062_, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v_a_472_);
return v___x_2072_;
}
}
else
{
lean_object* v_quotContext_2073_; lean_object* v_currMacroScope_2074_; lean_object* v_ref_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_quotContext_2073_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2074_ = lean_ctor_get(v_a_471_, 2);
v_ref_2075_ = lean_ctor_get(v_a_471_, 5);
v___x_2076_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
lean_dec(v___x_483_);
v___x_2077_ = l_Lean_SourceInfo_fromRef(v_ref_2075_, v___x_487_);
v___x_2078_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2079_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83);
v___x_2080_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85));
lean_inc(v_currMacroScope_2074_);
lean_inc(v_quotContext_2073_);
v___x_2081_ = l_Lean_addMacroScope(v_quotContext_2073_, v___x_2080_, v_currMacroScope_2074_);
v___x_2082_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__90));
lean_inc_n(v___x_2077_, 5);
v___x_2083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2077_);
lean_ctor_set(v___x_2083_, 1, v___x_2079_);
lean_ctor_set(v___x_2083_, 2, v___x_2081_);
lean_ctor_set(v___x_2083_, 3, v___x_2082_);
v___x_2084_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2085_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2077_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2077_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = l_Lean_Syntax_node3(v___x_2077_, v___x_477_, v___x_2086_, v___x_2076_, v___x_2088_);
v___x_2090_ = l_Lean_Syntax_node1(v___x_2077_, v___x_2084_, v___x_2089_);
v___x_2091_ = l_Lean_Syntax_node2(v___x_2077_, v___x_2078_, v___x_2083_, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_a_472_);
return v___x_2092_;
}
}
else
{
lean_object* v_quotContext_2093_; lean_object* v_currMacroScope_2094_; lean_object* v_ref_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_quotContext_2093_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2094_ = lean_ctor_get(v_a_471_, 2);
v_ref_2095_ = lean_ctor_get(v_a_471_, 5);
v___x_2096_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2097_ = lean_unsigned_to_nat(2u);
v___x_2098_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2097_);
lean_dec(v___x_483_);
v___x_2099_ = l_Lean_SourceInfo_fromRef(v_ref_2095_, v___x_485_);
v___x_2100_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2101_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92);
v___x_2102_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94));
lean_inc(v_currMacroScope_2094_);
lean_inc(v_quotContext_2093_);
v___x_2103_ = l_Lean_addMacroScope(v_quotContext_2093_, v___x_2102_, v_currMacroScope_2094_);
v___x_2104_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__97));
lean_inc_n(v___x_2099_, 6);
v___x_2105_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2099_);
lean_ctor_set(v___x_2105_, 1, v___x_2101_);
lean_ctor_set(v___x_2105_, 2, v___x_2103_);
lean_ctor_set(v___x_2105_, 3, v___x_2104_);
v___x_2106_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2107_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2099_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2099_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
lean_inc_ref(v___x_2110_);
lean_inc_ref(v___x_2108_);
v___x_2111_ = l_Lean_Syntax_node3(v___x_2099_, v___x_477_, v___x_2108_, v___x_2096_, v___x_2110_);
v___x_2112_ = l_Lean_Syntax_node3(v___x_2099_, v___x_477_, v___x_2108_, v___x_2098_, v___x_2110_);
v___x_2113_ = l_Lean_Syntax_node2(v___x_2099_, v___x_2106_, v___x_2111_, v___x_2112_);
v___x_2114_ = l_Lean_Syntax_node2(v___x_2099_, v___x_2100_, v___x_2105_, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_a_472_);
return v___x_2115_;
}
}
else
{
lean_object* v_quotContext_2116_; lean_object* v_currMacroScope_2117_; lean_object* v_ref_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_quotContext_2116_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2117_ = lean_ctor_get(v_a_471_, 2);
v_ref_2118_ = lean_ctor_get(v_a_471_, 5);
v___x_2119_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2120_ = lean_unsigned_to_nat(2u);
v___x_2121_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2120_);
lean_dec(v___x_483_);
v___x_2122_ = 0;
v___x_2123_ = l_Lean_SourceInfo_fromRef(v_ref_2118_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2125_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99);
v___x_2126_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101));
lean_inc(v_currMacroScope_2117_);
lean_inc(v_quotContext_2116_);
v___x_2127_ = l_Lean_addMacroScope(v_quotContext_2116_, v___x_2126_, v_currMacroScope_2117_);
v___x_2128_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__104));
lean_inc_n(v___x_2123_, 6);
v___x_2129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2123_);
lean_ctor_set(v___x_2129_, 1, v___x_2125_);
lean_ctor_set(v___x_2129_, 2, v___x_2127_);
lean_ctor_set(v___x_2129_, 3, v___x_2128_);
v___x_2130_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2131_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2123_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2123_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
lean_inc_ref(v___x_2134_);
lean_inc_ref(v___x_2132_);
v___x_2135_ = l_Lean_Syntax_node3(v___x_2123_, v___x_477_, v___x_2132_, v___x_2119_, v___x_2134_);
v___x_2136_ = l_Lean_Syntax_node3(v___x_2123_, v___x_477_, v___x_2132_, v___x_2121_, v___x_2134_);
v___x_2137_ = l_Lean_Syntax_node2(v___x_2123_, v___x_2130_, v___x_2135_, v___x_2136_);
v___x_2138_ = l_Lean_Syntax_node2(v___x_2123_, v___x_2124_, v___x_2129_, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v_a_472_);
return v___x_2139_;
}
}
v___jp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_box(1);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___y_474_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___boxed(lean_object* v_x_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1(v_x_2140_, v_a_2141_, v_a_2142_);
lean_dec_ref(v_a_2141_);
return v_res_2143_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0));
v___x_2146_ = l_String_toRawSubstring_x27(v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(lean_object* v_x_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
lean_inc(v_x_2160_);
v___x_2164_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_x_2160_);
v___x_2165_ = lean_box(1);
v___x_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v_a_2162_);
return v___x_2166_;
}
else
{
lean_object* v_quotContext_2167_; lean_object* v_currMacroScope_2168_; lean_object* v_ref_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_quotContext_2167_ = lean_ctor_get(v_a_2161_, 1);
v_currMacroScope_2168_ = lean_ctor_get(v_a_2161_, 2);
v_ref_2169_ = lean_ctor_get(v_a_2161_, 5);
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = l_Lean_Syntax_getArg(v_x_2160_, v___x_2170_);
lean_dec(v_x_2160_);
v___x_2172_ = 0;
v___x_2173_ = l_Lean_SourceInfo_fromRef(v_ref_2169_, v___x_2172_);
v___x_2174_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2175_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1);
v___x_2176_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3));
lean_inc_n(v_currMacroScope_2168_, 2);
lean_inc_n(v_quotContext_2167_, 2);
v___x_2177_ = l_Lean_addMacroScope(v_quotContext_2167_, v___x_2176_, v_currMacroScope_2168_);
v___x_2178_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8));
lean_inc_n(v___x_2173_, 9);
v___x_2179_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2173_);
lean_ctor_set(v___x_2179_, 1, v___x_2175_);
lean_ctor_set(v___x_2179_, 2, v___x_2177_);
lean_ctor_set(v___x_2179_, 3, v___x_2178_);
v___x_2180_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2181_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2182_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
v___x_2183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2173_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1);
v___x_2185_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_2186_ = l_Lean_addMacroScope(v_quotContext_2167_, v___x_2185_, v_currMacroScope_2168_);
v___x_2187_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__6));
v___x_2188_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2173_);
lean_ctor_set(v___x_2188_, 1, v___x_2184_);
lean_ctor_set(v___x_2188_, 2, v___x_2186_);
lean_ctor_set(v___x_2188_, 3, v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_2190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2173_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = l_Lean_Syntax_node3(v___x_2173_, v___x_2181_, v___x_2183_, v___x_2188_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2193_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2173_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2173_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = l_Lean_Syntax_node3(v___x_2173_, v___x_2192_, v___x_2194_, v___x_2171_, v___x_2196_);
v___x_2198_ = l_Lean_Syntax_node2(v___x_2173_, v___x_2180_, v___x_2191_, v___x_2197_);
v___x_2199_ = l_Lean_Syntax_node2(v___x_2173_, v___x_2174_, v___x_2179_, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v_a_2162_);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___boxed(lean_object* v_x_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(v_x_2201_, v_a_2202_, v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2204_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__0));
v___x_2207_ = l_String_toRawSubstring_x27(v___x_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(lean_object* v_x_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
lean_inc(v_x_2223_);
v___x_2227_ = l_Lean_Syntax_isOfKind(v_x_2223_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v_x_2223_);
v___x_2228_ = lean_box(1);
v___x_2229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v_a_2225_);
return v___x_2229_;
}
else
{
lean_object* v_quotContext_2230_; lean_object* v_currMacroScope_2231_; lean_object* v_ref_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_quotContext_2230_ = lean_ctor_get(v_a_2224_, 1);
v_currMacroScope_2231_ = lean_ctor_get(v_a_2224_, 2);
v_ref_2232_ = lean_ctor_get(v_a_2224_, 5);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = l_Lean_Syntax_getArg(v_x_2223_, v___x_2233_);
v___x_2235_ = lean_unsigned_to_nat(2u);
v___x_2236_ = l_Lean_Syntax_getArg(v_x_2223_, v___x_2235_);
lean_dec(v_x_2223_);
v___x_2237_ = 0;
v___x_2238_ = l_Lean_SourceInfo_fromRef(v_ref_2232_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2240_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1);
v___x_2241_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3));
lean_inc(v_currMacroScope_2231_);
lean_inc(v_quotContext_2230_);
v___x_2242_ = l_Lean_addMacroScope(v_quotContext_2230_, v___x_2241_, v_currMacroScope_2231_);
v___x_2243_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__6));
lean_inc_n(v___x_2238_, 6);
v___x_2244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2238_);
lean_ctor_set(v___x_2244_, 1, v___x_2240_);
lean_ctor_set(v___x_2244_, 2, v___x_2242_);
lean_ctor_set(v___x_2244_, 3, v___x_2243_);
v___x_2245_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2246_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2247_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2238_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2238_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
lean_inc_ref(v___x_2250_);
lean_inc_ref(v___x_2248_);
v___x_2251_ = l_Lean_Syntax_node3(v___x_2238_, v___x_2246_, v___x_2248_, v___x_2234_, v___x_2250_);
v___x_2252_ = l_Lean_Syntax_node3(v___x_2238_, v___x_2246_, v___x_2248_, v___x_2236_, v___x_2250_);
v___x_2253_ = l_Lean_Syntax_node2(v___x_2238_, v___x_2245_, v___x_2251_, v___x_2252_);
v___x_2254_ = l_Lean_Syntax_node2(v___x_2238_, v___x_2239_, v___x_2244_, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v_a_2225_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___boxed(lean_object* v_x_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(v_x_2256_, v_a_2257_, v_a_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure(lean_object* v_x_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2260_);
v___x_2264_ = l_Lean_Syntax_isOfKind(v_x_2260_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec(v_x_2260_);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v_a_2262_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = l_Lean_Syntax_getArg(v_x_2260_, v___x_2267_);
lean_dec(v_x_2260_);
v___x_2269_ = l_Lean_Syntax_getNumArgs(v___x_2268_);
v___x_2270_ = lean_nat_dec_le(v___x_2267_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec(v___x_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v_a_2262_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v_ts_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_Lean_Syntax_getArg(v___x_2268_, v___x_2273_);
v___x_2275_ = l_Lean_Syntax_getArgs(v___x_2268_);
lean_dec(v___x_2268_);
v___x_2276_ = l_Array_extract___redArg(v___x_2275_, v___x_2267_, v___x_2269_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2278_ = lean_box(2);
v___x_2279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v___x_2277_);
lean_ctor_set(v___x_2279_, 2, v___x_2276_);
v_ts_2280_ = l_Lean_Syntax_getArgs(v___x_2279_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = lean_array_get_size(v_ts_2280_);
v___x_2282_ = lean_nat_dec_eq(v___x_2281_, v___x_2273_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2283_ = l_Lean_SourceInfo_fromRef(v_a_2261_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2285_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc_n(v___x_2283_, 4);
v___x_2286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2283_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_2288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2283_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2284_, v___x_2286_, v___x_2274_, v___x_2288_);
v___x_2290_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2291_ = l_Array_append___redArg(v___x_2290_, v_ts_2280_);
lean_dec_ref(v_ts_2280_);
v___x_2292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2283_);
lean_ctor_set(v___x_2292_, 1, v___x_2277_);
lean_ctor_set(v___x_2292_, 2, v___x_2291_);
v___x_2293_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2263_, v___x_2289_, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v_a_2262_);
return v___x_2294_;
}
else
{
uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec_ref(v_ts_2280_);
v___x_2295_ = 0;
v___x_2296_ = l_Lean_SourceInfo_fromRef(v_a_2261_, v___x_2295_);
v___x_2297_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2298_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc_n(v___x_2296_, 2);
v___x_2299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2296_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_2301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2296_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_Syntax_node3(v___x_2296_, v___x_2297_, v___x_2299_, v___x_2274_, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_a_2262_);
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure___boxed(lean_object* v_x_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Std_Do_SPred_Notation_unexpandPure(v_x_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2305_);
return v_res_2307_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = lean_box(0);
v___x_2322_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__5));
v___x_2323_ = l_Lean_addMacroScope(v___x_2322_, v___x_2321_, v___x_2320_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(lean_object* v_x_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
lean_inc(v_x_2350_);
v___x_2354_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
lean_inc(v_x_2350_);
v___x_2356_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__1));
lean_inc(v_x_2350_);
v___x_2358_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_2360_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v_x_2350_);
v___x_2361_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3));
lean_inc(v_x_2350_);
v___x_2363_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_x_2350_);
lean_ctor_set(v___x_2364_, 1, v___y_2352_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2365_);
v___x_2367_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_2366_);
v___x_2368_ = l_Lean_Syntax_isOfKind(v___x_2366_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_dec(v___x_2366_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_x_2350_);
lean_ctor_set(v___x_2369_, 1, v___y_2352_);
return v___x_2369_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2370_ = lean_unsigned_to_nat(1u);
v___x_2371_ = l_Lean_Syntax_getArg(v___x_2366_, v___x_2370_);
lean_dec(v___x_2366_);
v___x_2372_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_2371_);
v___x_2373_ = l_Lean_Syntax_isOfKind(v___x_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_dec(v___x_2371_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_x_2350_);
lean_ctor_set(v___x_2374_, 1, v___y_2352_);
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2375_ = l_Lean_Syntax_getArg(v___x_2371_, v___x_2365_);
lean_dec(v___x_2371_);
v___x_2376_ = lean_box(0);
v___x_2377_ = l_Lean_Syntax_matchesIdent(v___x_2375_, v___x_2376_);
lean_dec(v___x_2375_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_x_2350_);
lean_ctor_set(v___x_2378_, 1, v___y_2352_);
return v___x_2378_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2379_ = lean_unsigned_to_nat(3u);
v___x_2380_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2379_);
lean_inc(v___x_2380_);
v___x_2381_ = l_Lean_Syntax_matchesNull(v___x_2380_, v___x_2370_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
lean_dec(v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_x_2350_);
lean_ctor_set(v___x_2382_, 1, v___y_2352_);
return v___x_2382_;
}
else
{
lean_object* v_P_2383_; lean_object* v___x_2384_; 
v_P_2383_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2370_);
lean_dec(v_x_2350_);
v___x_2384_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2383_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2410_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_a_2386_ = lean_ctor_get(v___x_2384_, 1);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2388_ = v___x_2384_;
v_isShared_2389_ = v_isSharedCheck_2410_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2410_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2390_ = l_Lean_Syntax_getArg(v___x_2380_, v___x_2365_);
lean_dec(v___x_2380_);
v___x_2391_ = l_Lean_SourceInfo_fromRef(v___y_2351_, v___x_2361_);
v___x_2392_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc_n(v___x_2391_, 7);
v___x_2393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2395_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_2396_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
v___x_2397_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2391_);
lean_ctor_set(v___x_2397_, 1, v___x_2394_);
lean_ctor_set(v___x_2397_, 2, v___x_2395_);
lean_ctor_set(v___x_2397_, 3, v___x_2396_);
v___x_2398_ = l_Lean_Syntax_node1(v___x_2391_, v___x_2372_, v___x_2397_);
v___x_2399_ = l_Lean_Syntax_node2(v___x_2391_, v___x_2367_, v___x_2393_, v___x_2398_);
v___x_2400_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_2401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2391_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2403_ = l_Lean_Syntax_node1(v___x_2391_, v___x_2402_, v___x_2390_);
v___x_2404_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2391_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = l_Lean_Syntax_node5(v___x_2391_, v___x_2362_, v___x_2399_, v_a_2385_, v___x_2401_, v___x_2403_, v___x_2405_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2406_);
v___x_2408_ = v___x_2388_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_a_2386_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
else
{
lean_dec(v___x_2380_);
return v___x_2384_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2411_ = lean_unsigned_to_nat(1u);
v___x_2412_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2411_);
v___x_2413_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_2412_);
v___x_2414_ = l_Lean_Syntax_isOfKind(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_dec(v___x_2412_);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v_x_2350_);
lean_ctor_set(v___x_2415_, 1, v___y_2352_);
return v___x_2415_;
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2416_ = lean_unsigned_to_nat(0u);
v___x_2417_ = l_Lean_Syntax_getArg(v___x_2412_, v___x_2411_);
v___x_2418_ = l_Lean_Syntax_matchesNull(v___x_2417_, v___x_2416_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
lean_dec(v___x_2412_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_x_2350_);
lean_ctor_set(v___x_2419_, 1, v___y_2352_);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; lean_object* v_b_2421_; lean_object* v___x_2422_; 
lean_dec(v_x_2350_);
v___x_2420_ = lean_unsigned_to_nat(3u);
v_b_2421_ = l_Lean_Syntax_getArg(v___x_2412_, v___x_2420_);
v___x_2422_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_b_2421_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2444_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_a_2424_ = lean_ctor_get(v___x_2422_, 1);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2426_ = v___x_2422_;
v_isShared_2427_ = v_isSharedCheck_2444_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2444_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v_xs_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2428_ = l_Lean_Syntax_getArg(v___x_2412_, v___x_2416_);
lean_dec(v___x_2412_);
v_xs_2429_ = l_Lean_Syntax_getArgs(v___x_2428_);
lean_dec(v___x_2428_);
v___x_2430_ = l_Lean_SourceInfo_fromRef(v___y_2351_, v___x_2358_);
lean_inc_n(v___x_2430_, 5);
v___x_2431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v___x_2359_);
v___x_2432_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2433_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2434_ = l_Array_append___redArg(v___x_2433_, v_xs_2429_);
lean_dec_ref(v_xs_2429_);
v___x_2435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2430_);
lean_ctor_set(v___x_2435_, 1, v___x_2432_);
lean_ctor_set(v___x_2435_, 2, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2430_);
lean_ctor_set(v___x_2436_, 1, v___x_2432_);
lean_ctor_set(v___x_2436_, 2, v___x_2433_);
v___x_2437_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2430_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = l_Lean_Syntax_node4(v___x_2430_, v___x_2413_, v___x_2435_, v___x_2436_, v___x_2438_, v_a_2423_);
v___x_2440_ = l_Lean_Syntax_node2(v___x_2430_, v___x_2360_, v___x_2431_, v___x_2439_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2440_);
v___x_2442_ = v___x_2426_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_a_2424_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
else
{
lean_dec(v___x_2412_);
return v___x_2422_;
}
}
}
}
}
else
{
lean_object* v___x_2445_; lean_object* v_t_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_unsigned_to_nat(3u);
v_t_2446_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2445_);
v___x_2447_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_t_2446_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2477_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_a_2449_ = lean_ctor_get(v___x_2447_, 1);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2451_ = v___x_2447_;
v_isShared_2452_ = v_isSharedCheck_2477_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2477_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v_e_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_unsigned_to_nat(5u);
v_e_2454_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2453_);
v___x_2455_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_e_2454_, v___y_2351_, v_a_2449_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2476_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_a_2457_ = lean_ctor_get(v___x_2455_, 1);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2459_ = v___x_2455_;
v_isShared_2460_ = v_isSharedCheck_2476_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2476_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2461_ = lean_unsigned_to_nat(1u);
v___x_2462_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2461_);
lean_dec(v_x_2350_);
v___x_2463_ = l_Lean_SourceInfo_fromRef(v___y_2351_, v___x_2356_);
v___x_2464_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__15));
lean_inc(v___x_2463_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set_tag(v___x_2451_, 2);
lean_ctor_set(v___x_2451_, 1, v___x_2464_);
lean_ctor_set(v___x_2451_, 0, v___x_2463_);
v___x_2466_ = v___x_2451_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2467_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__16));
lean_inc_n(v___x_2463_, 2);
v___x_2468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2463_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__17));
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2463_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_Syntax_node6(v___x_2463_, v___x_2357_, v___x_2466_, v___x_2462_, v___x_2468_, v_a_2448_, v___x_2470_, v_a_2456_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2471_);
v___x_2473_ = v___x_2459_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_a_2457_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_del_object(v___x_2451_);
lean_dec(v_a_2448_);
lean_dec(v_x_2350_);
return v___x_2455_;
}
}
}
else
{
lean_dec(v_x_2350_);
return v___x_2447_;
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2478_);
v___x_2480_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_2479_);
v___x_2481_ = l_Lean_Syntax_isOfKind(v___x_2479_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
lean_dec(v___x_2479_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_x_2350_);
lean_ctor_set(v___x_2482_, 1, v___y_2352_);
return v___x_2482_;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2483_ = lean_unsigned_to_nat(1u);
v___x_2484_ = l_Lean_Syntax_getArg(v___x_2479_, v___x_2483_);
lean_dec(v___x_2479_);
v___x_2485_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_2484_);
v___x_2486_ = l_Lean_Syntax_isOfKind(v___x_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec(v___x_2484_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v_x_2350_);
lean_ctor_set(v___x_2487_, 1, v___y_2352_);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2488_ = l_Lean_Syntax_getArg(v___x_2484_, v___x_2478_);
lean_dec(v___x_2484_);
v___x_2489_ = lean_box(0);
v___x_2490_ = l_Lean_Syntax_matchesIdent(v___x_2488_, v___x_2489_);
lean_dec(v___x_2488_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v_x_2350_);
lean_ctor_set(v___x_2491_, 1, v___y_2352_);
return v___x_2491_;
}
else
{
lean_object* v_P_2492_; lean_object* v___x_2493_; 
v_P_2492_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2483_);
lean_dec(v_x_2350_);
v___x_2493_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2492_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2514_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_a_2495_ = lean_ctor_get(v___x_2493_, 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2497_ = v___x_2493_;
v_isShared_2498_ = v_isSharedCheck_2514_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2514_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2499_ = l_Lean_SourceInfo_fromRef(v___y_2351_, v___x_2354_);
v___x_2500_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc_n(v___x_2499_, 5);
v___x_2501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2503_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_2504_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
v___x_2505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2499_);
lean_ctor_set(v___x_2505_, 1, v___x_2502_);
lean_ctor_set(v___x_2505_, 2, v___x_2503_);
lean_ctor_set(v___x_2505_, 3, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_node1(v___x_2499_, v___x_2485_, v___x_2505_);
v___x_2507_ = l_Lean_Syntax_node2(v___x_2499_, v___x_2480_, v___x_2501_, v___x_2506_);
v___x_2508_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2499_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = l_Lean_Syntax_node3(v___x_2499_, v___x_2355_, v___x_2507_, v_a_2494_, v___x_2509_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2510_);
v___x_2512_ = v___x_2497_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_a_2495_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
return v___x_2493_;
}
}
}
}
}
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_unsigned_to_nat(1u);
v___x_2516_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2515_);
lean_dec(v_x_2350_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
lean_ctor_set(v___x_2517_, 1, v___y_2352_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___boxed(lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_x_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails(lean_object* v_x_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2523_);
v___x_2527_ = l_Lean_Syntax_isOfKind(v_x_2523_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v_x_2523_);
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v_a_2525_);
return v___x_2529_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = l_Lean_Syntax_getArg(v_x_2523_, v___x_2530_);
lean_dec(v_x_2523_);
v___x_2532_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2531_);
v___x_2533_ = l_Lean_Syntax_matchesNull(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v___x_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v_a_2525_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v_P_2537_; lean_object* v___x_2538_; 
v___x_2536_ = lean_unsigned_to_nat(0u);
v_P_2537_ = l_Lean_Syntax_getArg(v___x_2531_, v___x_2536_);
v___x_2538_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2537_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_a_2540_; lean_object* v_Q_2541_; lean_object* v___x_2542_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
v_a_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_a_2540_);
lean_dec_ref(v___x_2538_);
v_Q_2541_ = l_Lean_Syntax_getArg(v___x_2531_, v___x_2530_);
lean_dec(v___x_2531_);
v___x_2542_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2541_, v_a_2524_, v_a_2540_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2578_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_a_2544_ = lean_ctor_get(v___x_2542_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2546_ = v___x_2542_;
v_isShared_2547_ = v_isSharedCheck_2578_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2578_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
lean_inc(v_a_2539_);
v___x_2549_ = l_Lean_Syntax_isOfKind(v_a_2539_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2550_ = l_Lean_SourceInfo_fromRef(v_a_2524_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_2552_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2550_);
v___x_2553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2550_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node3(v___x_2550_, v___x_2551_, v_a_2539_, v___x_2553_, v_a_2543_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2554_);
v___x_2556_ = v___x_2546_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_a_2544_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = l_Lean_Syntax_getArg(v_a_2539_, v___x_2530_);
v___x_2559_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_2560_ = l_Lean_Syntax_matchesIdent(v___x_2558_, v___x_2559_);
lean_dec(v___x_2558_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2561_ = l_Lean_SourceInfo_fromRef(v_a_2524_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_2563_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2561_);
v___x_2564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2561_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node3(v___x_2561_, v___x_2562_, v_a_2539_, v___x_2564_, v_a_2543_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2565_);
v___x_2567_ = v___x_2546_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_a_2544_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
else
{
uint8_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_dec(v_a_2539_);
v___x_2569_ = 0;
v___x_2570_ = l_Lean_SourceInfo_fromRef(v_a_2524_, v___x_2569_);
v___x_2571_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
v___x_2572_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2570_);
v___x_2573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2570_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_node2(v___x_2570_, v___x_2571_, v___x_2573_, v_a_2543_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2574_);
v___x_2576_ = v___x_2546_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_a_2544_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_a_2539_);
v_a_2579_ = lean_ctor_get(v___x_2542_, 0);
v_a_2580_ = lean_ctor_get(v___x_2542_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2542_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_inc(v_a_2579_);
lean_dec(v___x_2542_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2579_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v___x_2531_);
v_a_2588_ = lean_ctor_get(v___x_2538_, 0);
v_a_2589_ = lean_ctor_get(v___x_2538_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2538_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_inc(v_a_2588_);
lean_dec(v___x_2538_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2588_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails___boxed(lean_object* v_x_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Std_Do_SPred_Notation_unexpandEntails(v_x_2597_, v_a_2598_, v_a_2599_);
lean_dec(v_a_2598_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails(lean_object* v_x_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2602_);
v___x_2606_ = l_Lean_Syntax_isOfKind(v_x_2602_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec(v_x_2602_);
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v_a_2604_);
return v___x_2608_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = l_Lean_Syntax_getArg(v_x_2602_, v___x_2609_);
lean_dec(v_x_2602_);
v___x_2611_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2610_);
v___x_2612_ = l_Lean_Syntax_matchesNull(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v_a_2604_);
return v___x_2614_;
}
else
{
lean_object* v___x_2615_; lean_object* v_P_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_unsigned_to_nat(0u);
v_P_2616_ = l_Lean_Syntax_getArg(v___x_2610_, v___x_2615_);
v___x_2617_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2616_, v_a_2603_, v_a_2604_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v_a_2619_; lean_object* v_Q_2620_; lean_object* v___x_2621_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
v_a_2619_ = lean_ctor_get(v___x_2617_, 1);
lean_inc(v_a_2619_);
lean_dec_ref(v___x_2617_);
v_Q_2620_ = l_Lean_Syntax_getArg(v___x_2610_, v___x_2609_);
lean_dec(v___x_2610_);
v___x_2621_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2620_, v_a_2603_, v_a_2619_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2636_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_a_2623_ = lean_ctor_get(v___x_2621_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2625_ = v___x_2621_;
v_isShared_2626_ = v_isSharedCheck_2636_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2636_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2627_ = 0;
v___x_2628_ = l_Lean_SourceInfo_fromRef(v_a_2603_, v___x_2627_);
v___x_2629_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
v___x_2630_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandBientails___closed__0));
lean_inc(v___x_2628_);
v___x_2631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2628_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_Syntax_node3(v___x_2628_, v___x_2629_, v_a_2618_, v___x_2631_, v_a_2622_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2632_);
v___x_2634_ = v___x_2625_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_a_2623_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_a_2618_);
v_a_2637_ = lean_ctor_get(v___x_2621_, 0);
v_a_2638_ = lean_ctor_get(v___x_2621_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2621_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_inc(v_a_2637_);
lean_dec(v___x_2621_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2637_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v___x_2610_);
v_a_2646_ = lean_ctor_get(v___x_2617_, 0);
v_a_2647_ = lean_ctor_get(v___x_2617_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2617_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_inc(v_a_2646_);
lean_dec(v___x_2617_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails___boxed(lean_object* v_x_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_Do_SPred_Notation_unexpandBientails(v_x_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd(lean_object* v_x_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2660_);
v___x_2664_ = l_Lean_Syntax_isOfKind(v_x_2660_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v_x_2660_);
v___x_2665_ = lean_box(0);
v___x_2666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v_a_2662_);
return v___x_2666_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = l_Lean_Syntax_getArg(v_x_2660_, v___x_2667_);
lean_dec(v_x_2660_);
v___x_2669_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2668_);
v___x_2670_ = l_Lean_Syntax_matchesNull(v___x_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v___x_2672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v_a_2662_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; lean_object* v_P_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_unsigned_to_nat(0u);
v_P_2674_ = l_Lean_Syntax_getArg(v___x_2668_, v___x_2673_);
v___x_2675_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2674_, v_a_2661_, v_a_2662_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v_a_2677_; lean_object* v_Q_2678_; lean_object* v___x_2679_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
v_a_2677_ = lean_ctor_get(v___x_2675_, 1);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2675_);
v_Q_2678_ = l_Lean_Syntax_getArg(v___x_2668_, v___x_2667_);
lean_dec(v___x_2668_);
v___x_2679_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2678_, v_a_2661_, v_a_2677_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2700_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_a_2681_ = lean_ctor_get(v___x_2679_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2683_ = v___x_2679_;
v_isShared_2684_ = v_isSharedCheck_2700_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2700_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2685_ = 0;
v___x_2686_ = l_Lean_SourceInfo_fromRef(v_a_2661_, v___x_2685_);
v___x_2687_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2688_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2686_, 4);
v___x_2689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2686_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1));
v___x_2691_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandAnd___closed__0));
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2686_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_Syntax_node3(v___x_2686_, v___x_2690_, v_a_2676_, v___x_2692_, v_a_2680_);
v___x_2694_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2686_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_Syntax_node3(v___x_2686_, v___x_2687_, v___x_2689_, v___x_2693_, v___x_2695_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2696_);
v___x_2698_ = v___x_2683_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_a_2681_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec(v_a_2676_);
v_a_2701_ = lean_ctor_get(v___x_2679_, 0);
v_a_2702_ = lean_ctor_get(v___x_2679_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2679_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_inc(v_a_2701_);
lean_dec(v___x_2679_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2701_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v___x_2668_);
v_a_2710_ = lean_ctor_get(v___x_2675_, 0);
v_a_2711_ = lean_ctor_get(v___x_2675_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2675_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_inc(v_a_2710_);
lean_dec(v___x_2675_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2710_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd___boxed(lean_object* v_x_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_Do_SPred_Notation_unexpandAnd(v_x_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr(lean_object* v_x_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2724_);
v___x_2728_ = l_Lean_Syntax_isOfKind(v_x_2724_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec(v_x_2724_);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v_a_2726_);
return v___x_2730_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2731_ = lean_unsigned_to_nat(1u);
v___x_2732_ = l_Lean_Syntax_getArg(v_x_2724_, v___x_2731_);
lean_dec(v_x_2724_);
v___x_2733_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2732_);
v___x_2734_ = l_Lean_Syntax_matchesNull(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
lean_ctor_set(v___x_2736_, 1, v_a_2726_);
return v___x_2736_;
}
else
{
lean_object* v___x_2737_; lean_object* v_P_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_unsigned_to_nat(0u);
v_P_2738_ = l_Lean_Syntax_getArg(v___x_2732_, v___x_2737_);
v___x_2739_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2738_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v_a_2741_; lean_object* v_Q_2742_; lean_object* v___x_2743_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
v_a_2741_ = lean_ctor_get(v___x_2739_, 1);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2739_);
v_Q_2742_ = l_Lean_Syntax_getArg(v___x_2732_, v___x_2731_);
lean_dec(v___x_2732_);
v___x_2743_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2742_, v_a_2725_, v_a_2741_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2764_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_a_2745_ = lean_ctor_get(v___x_2743_, 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2747_ = v___x_2743_;
v_isShared_2748_ = v_isSharedCheck_2764_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2764_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2749_ = 0;
v___x_2750_ = l_Lean_SourceInfo_fromRef(v_a_2725_, v___x_2749_);
v___x_2751_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2752_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2750_, 4);
v___x_2753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2750_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3));
v___x_2755_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandOr___closed__0));
v___x_2756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2750_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_Syntax_node3(v___x_2750_, v___x_2754_, v_a_2740_, v___x_2756_, v_a_2744_);
v___x_2758_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2750_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l_Lean_Syntax_node3(v___x_2750_, v___x_2751_, v___x_2753_, v___x_2757_, v___x_2759_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2760_);
v___x_2762_ = v___x_2747_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_a_2745_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2740_);
v_a_2765_ = lean_ctor_get(v___x_2743_, 0);
v_a_2766_ = lean_ctor_get(v___x_2743_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2743_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_inc(v_a_2765_);
lean_dec(v___x_2743_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2765_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v___x_2732_);
v_a_2774_ = lean_ctor_get(v___x_2739_, 0);
v_a_2775_ = lean_ctor_get(v___x_2739_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2739_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_inc(v_a_2774_);
lean_dec(v___x_2739_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2774_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr___boxed(lean_object* v_x_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Std_Do_SPred_Notation_unexpandOr(v_x_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2784_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot(lean_object* v_x_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2788_);
v___x_2792_ = l_Lean_Syntax_isOfKind(v_x_2788_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec(v_x_2788_);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v_a_2790_);
return v___x_2794_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = l_Lean_Syntax_getArg(v_x_2788_, v___x_2795_);
lean_dec(v_x_2788_);
lean_inc(v___x_2796_);
v___x_2797_ = l_Lean_Syntax_matchesNull(v___x_2796_, v___x_2795_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec(v___x_2796_);
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v_a_2790_);
return v___x_2799_;
}
else
{
lean_object* v___x_2800_; lean_object* v_P_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_unsigned_to_nat(0u);
v_P_2801_ = l_Lean_Syntax_getArg(v___x_2796_, v___x_2800_);
lean_dec(v___x_2796_);
v___x_2802_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2801_, v_a_2789_, v_a_2790_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2823_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_a_2804_ = lean_ctor_get(v___x_2802_, 1);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2806_ = v___x_2802_;
v_isShared_2807_ = v_isSharedCheck_2823_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2823_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
uint8_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2808_ = 0;
v___x_2809_ = l_Lean_SourceInfo_fromRef(v_a_2789_, v___x_2808_);
v___x_2810_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2811_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2809_, 4);
v___x_2812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2809_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5));
v___x_2814_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandNot___closed__0));
v___x_2815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2809_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = l_Lean_Syntax_node2(v___x_2809_, v___x_2813_, v___x_2815_, v_a_2803_);
v___x_2817_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2809_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = l_Lean_Syntax_node3(v___x_2809_, v___x_2810_, v___x_2812_, v___x_2816_, v___x_2818_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2819_);
v___x_2821_ = v___x_2806_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_a_2804_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2824_ = lean_ctor_get(v___x_2802_, 0);
v_a_2825_ = lean_ctor_get(v___x_2802_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2802_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_inc(v_a_2824_);
lean_dec(v___x_2802_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2824_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot___boxed(lean_object* v_x_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Std_Do_SPred_Notation_unexpandNot(v_x_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2834_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp(lean_object* v_x_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2838_);
v___x_2842_ = l_Lean_Syntax_isOfKind(v_x_2838_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec(v_x_2838_);
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v_a_2840_);
return v___x_2844_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2845_ = lean_unsigned_to_nat(1u);
v___x_2846_ = l_Lean_Syntax_getArg(v_x_2838_, v___x_2845_);
lean_dec(v_x_2838_);
v___x_2847_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2846_);
v___x_2848_ = l_Lean_Syntax_matchesNull(v___x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v_a_2840_);
return v___x_2850_;
}
else
{
lean_object* v___x_2851_; lean_object* v_P_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_unsigned_to_nat(0u);
v_P_2852_ = l_Lean_Syntax_getArg(v___x_2846_, v___x_2851_);
v___x_2853_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2852_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v_a_2855_; lean_object* v_Q_2856_; lean_object* v___x_2857_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
v_a_2855_ = lean_ctor_get(v___x_2853_, 1);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2853_);
v_Q_2856_ = l_Lean_Syntax_getArg(v___x_2846_, v___x_2845_);
lean_dec(v___x_2846_);
v___x_2857_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2856_, v_a_2839_, v_a_2855_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2878_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_a_2859_ = lean_ctor_get(v___x_2857_, 1);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2861_ = v___x_2857_;
v_isShared_2862_ = v_isSharedCheck_2878_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2878_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2863_ = 0;
v___x_2864_ = l_Lean_SourceInfo_fromRef(v_a_2839_, v___x_2863_);
v___x_2865_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2866_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2864_, 4);
v___x_2867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2864_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7));
v___x_2869_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandImp___closed__0));
v___x_2870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2864_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = l_Lean_Syntax_node3(v___x_2864_, v___x_2868_, v_a_2854_, v___x_2870_, v_a_2858_);
v___x_2872_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2864_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = l_Lean_Syntax_node3(v___x_2864_, v___x_2865_, v___x_2867_, v___x_2871_, v___x_2873_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2874_);
v___x_2876_ = v___x_2861_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_a_2859_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2854_);
v_a_2879_ = lean_ctor_get(v___x_2857_, 0);
v_a_2880_ = lean_ctor_get(v___x_2857_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2857_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_inc(v_a_2879_);
lean_dec(v___x_2857_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2879_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v___x_2846_);
v_a_2888_ = lean_ctor_get(v___x_2853_, 0);
v_a_2889_ = lean_ctor_get(v___x_2853_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2853_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_inc(v_a_2888_);
lean_dec(v___x_2853_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2888_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp___boxed(lean_object* v_x_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Std_Do_SPred_Notation_unexpandImp(v_x_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(size_t v_sz_2901_, size_t v_i_2902_, lean_object* v_bs_2903_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_usize_dec_lt(v_i_2902_, v_sz_2901_);
if (v___x_2904_ == 0)
{
return v_bs_2903_;
}
else
{
lean_object* v_v_2905_; lean_object* v___x_2906_; lean_object* v_bs_x27_2907_; size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v_v_2905_ = lean_array_uget(v_bs_2903_, v_i_2902_);
v___x_2906_ = lean_unsigned_to_nat(0u);
v_bs_x27_2907_ = lean_array_uset(v_bs_2903_, v_i_2902_, v___x_2906_);
v___x_2908_ = ((size_t)1ULL);
v___x_2909_ = lean_usize_add(v_i_2902_, v___x_2908_);
v___x_2910_ = lean_array_uset(v_bs_x27_2907_, v_i_2902_, v_v_2905_);
v_i_2902_ = v___x_2909_;
v_bs_2903_ = v___x_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1___boxed(lean_object* v_sz_2912_, lean_object* v_i_2913_, lean_object* v_bs_2914_){
_start:
{
size_t v_sz_boxed_2915_; size_t v_i_boxed_2916_; lean_object* v_res_2917_; 
v_sz_boxed_2915_ = lean_unbox_usize(v_sz_2912_);
lean_dec(v_sz_2912_);
v_i_boxed_2916_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_boxed_2915_, v_i_boxed_2916_, v_bs_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(size_t v_sz_2918_, size_t v_i_2919_, lean_object* v_bs_2920_){
_start:
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_usize_dec_lt(v_i_2919_, v_sz_2918_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_bs_2920_);
return v___x_2922_;
}
else
{
lean_object* v_v_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v_v_2923_ = lean_array_uget(v_bs_2920_, v_i_2919_);
v___x_2924_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_v_2923_);
v___x_2925_ = l_Lean_Syntax_isOfKind(v_v_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; 
lean_dec(v_v_2923_);
lean_dec_ref(v_bs_2920_);
v___x_2926_ = lean_box(0);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; lean_object* v_bs_x27_2928_; size_t v___x_2929_; size_t v___x_2930_; lean_object* v___x_2931_; 
v___x_2927_ = lean_unsigned_to_nat(0u);
v_bs_x27_2928_ = lean_array_uset(v_bs_2920_, v_i_2919_, v___x_2927_);
v___x_2929_ = ((size_t)1ULL);
v___x_2930_ = lean_usize_add(v_i_2919_, v___x_2929_);
v___x_2931_ = lean_array_uset(v_bs_x27_2928_, v_i_2919_, v_v_2923_);
v_i_2919_ = v___x_2930_;
v_bs_2920_ = v___x_2931_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0___boxed(lean_object* v_sz_2933_, lean_object* v_i_2934_, lean_object* v_bs_2935_){
_start:
{
size_t v_sz_boxed_2936_; size_t v_i_boxed_2937_; lean_object* v_res_2938_; 
v_sz_boxed_2936_ = lean_unbox_usize(v_sz_2933_);
lean_dec(v_sz_2933_);
v_i_boxed_2937_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_boxed_2936_, v_i_boxed_2937_, v_bs_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall(lean_object* v_x_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2942_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2939_);
v___x_2943_ = l_Lean_Syntax_isOfKind(v_x_2939_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v_x_2939_);
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v_a_2941_);
return v___x_2945_;
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2946_ = lean_unsigned_to_nat(1u);
v___x_2947_ = l_Lean_Syntax_getArg(v_x_2939_, v___x_2946_);
lean_dec(v_x_2939_);
lean_inc(v___x_2947_);
v___x_2948_ = l_Lean_Syntax_matchesNull(v___x_2947_, v___x_2946_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_dec(v___x_2947_);
v___x_2949_ = lean_box(0);
v___x_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v_a_2941_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = l_Lean_Syntax_getArg(v___x_2947_, v___x_2951_);
lean_dec(v___x_2947_);
v___x_2953_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_2952_);
v___x_2954_ = l_Lean_Syntax_isOfKind(v___x_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v_a_2941_);
return v___x_2956_;
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2957_ = l_Lean_Syntax_getArg(v___x_2952_, v___x_2946_);
lean_dec(v___x_2952_);
v___x_2958_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_2957_);
v___x_2959_ = l_Lean_Syntax_isOfKind(v___x_2957_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v_a_2941_);
return v___x_2961_;
}
else
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = l_Lean_Syntax_getArg(v___x_2957_, v___x_2951_);
lean_inc(v___x_2962_);
v___x_2963_ = l_Lean_Syntax_matchesNull(v___x_2962_, v___x_2946_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v___x_2962_);
lean_dec(v___x_2957_);
v___x_2964_ = lean_box(0);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v_a_2941_);
return v___x_2965_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2966_ = l_Lean_Syntax_getArg(v___x_2962_, v___x_2951_);
lean_dec(v___x_2962_);
v___x_2967_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_2966_);
v___x_2968_ = l_Lean_Syntax_isOfKind(v___x_2966_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec(v___x_2966_);
lean_dec(v___x_2957_);
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2941_);
return v___x_2970_;
}
else
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = l_Lean_Syntax_getArg(v___x_2957_, v___x_2946_);
v___x_2972_ = l_Lean_Syntax_matchesNull(v___x_2971_, v___x_2951_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec(v___x_2966_);
lean_dec(v___x_2957_);
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v_a_2941_);
return v___x_2974_;
}
else
{
lean_object* v___x_2975_; lean_object* v_00_u03a8_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2975_ = lean_unsigned_to_nat(3u);
v_00_u03a8_2976_ = l_Lean_Syntax_getArg(v___x_2957_, v___x_2975_);
lean_dec(v___x_2957_);
v___x_2977_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13));
lean_inc(v_00_u03a8_2976_);
v___x_2978_ = l_Lean_Syntax_isOfKind(v_00_u03a8_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2976_, v_a_2940_, v_a_2941_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3004_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_a_2981_ = lean_ctor_get(v___x_2979_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_3004_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3004_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_2985_ = l_Lean_SourceInfo_fromRef(v_a_2940_, v___x_2978_);
v___x_2986_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2987_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2985_, 7);
v___x_2988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2985_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_2990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2985_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2992_ = l_Lean_Syntax_node1(v___x_2985_, v___x_2991_, v___x_2966_);
v___x_2993_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2985_);
lean_ctor_set(v___x_2994_, 1, v___x_2991_);
lean_ctor_set(v___x_2994_, 2, v___x_2993_);
v___x_2995_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2985_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = l_Lean_Syntax_node5(v___x_2985_, v___x_2977_, v___x_2990_, v___x_2992_, v___x_2994_, v___x_2996_, v_a_2980_);
v___x_2998_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2985_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_Lean_Syntax_node3(v___x_2985_, v___x_2986_, v___x_2988_, v___x_2997_, v___x_2999_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_3000_);
v___x_3002_ = v___x_2983_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_a_2981_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v___x_2966_);
v_a_3005_ = lean_ctor_get(v___x_2979_, 0);
v_a_3006_ = lean_ctor_get(v___x_2979_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2979_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_inc(v_a_3005_);
lean_dec(v___x_2979_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3005_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3014_ = l_Lean_Syntax_getArg(v_00_u03a8_2976_, v___x_2946_);
v___x_3015_ = l_Lean_Syntax_getNumArgs(v___x_3014_);
v___x_3016_ = lean_nat_dec_le(v___x_2946_, v___x_3015_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
lean_dec(v___x_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2976_, v_a_2940_, v_a_2941_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3042_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_a_3019_ = lean_ctor_get(v___x_3017_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3021_ = v___x_3017_;
v_isShared_3022_ = v_isSharedCheck_3042_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3042_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3023_ = l_Lean_SourceInfo_fromRef(v_a_2940_, v___x_3016_);
v___x_3024_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3025_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3023_, 7);
v___x_3026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3023_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3023_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3030_ = l_Lean_Syntax_node1(v___x_3023_, v___x_3029_, v___x_2966_);
v___x_3031_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3023_);
lean_ctor_set(v___x_3032_, 1, v___x_3029_);
lean_ctor_set(v___x_3032_, 2, v___x_3031_);
v___x_3033_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3023_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = l_Lean_Syntax_node5(v___x_3023_, v___x_2977_, v___x_3028_, v___x_3030_, v___x_3032_, v___x_3034_, v_a_3018_);
v___x_3036_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3023_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Lean_Syntax_node3(v___x_3023_, v___x_3024_, v___x_3026_, v___x_3035_, v___x_3037_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3038_);
v___x_3040_ = v___x_3021_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_a_3019_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v___x_2966_);
v_a_3043_ = lean_ctor_get(v___x_3017_, 0);
v_a_3044_ = lean_ctor_get(v___x_3017_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3017_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_inc(v_a_3043_);
lean_dec(v___x_3017_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3043_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = l_Lean_Syntax_getArg(v___x_3014_, v___x_2951_);
lean_inc(v___x_3052_);
v___x_3053_ = l_Lean_Syntax_isOfKind(v___x_3052_, v___x_2967_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
lean_dec(v___x_3052_);
lean_dec(v___x_3015_);
lean_dec(v___x_3014_);
v___x_3054_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2976_, v_a_2940_, v_a_2941_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3079_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_a_3056_ = lean_ctor_get(v___x_3054_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3058_ = v___x_3054_;
v_isShared_3059_ = v_isSharedCheck_3079_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3079_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3060_ = l_Lean_SourceInfo_fromRef(v_a_2940_, v___x_3053_);
v___x_3061_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3062_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3060_, 7);
v___x_3063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3060_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3060_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3067_ = l_Lean_Syntax_node1(v___x_3060_, v___x_3066_, v___x_2966_);
v___x_3068_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3060_);
lean_ctor_set(v___x_3069_, 1, v___x_3066_);
lean_ctor_set(v___x_3069_, 2, v___x_3068_);
v___x_3070_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3060_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = l_Lean_Syntax_node5(v___x_3060_, v___x_2977_, v___x_3065_, v___x_3067_, v___x_3069_, v___x_3071_, v_a_3055_);
v___x_3073_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3060_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = l_Lean_Syntax_node3(v___x_3060_, v___x_3061_, v___x_3063_, v___x_3072_, v___x_3074_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3075_);
v___x_3077_ = v___x_3058_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_a_3056_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v___x_2966_);
v_a_3080_ = lean_ctor_get(v___x_3054_, 0);
v_a_3081_ = lean_ctor_get(v___x_3054_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3054_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_inc(v_a_3080_);
lean_dec(v___x_3054_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3080_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; size_t v_sz_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v___x_3089_ = l_Lean_Syntax_getArgs(v___x_3014_);
lean_dec(v___x_3014_);
v___x_3090_ = l_Array_extract___redArg(v___x_3089_, v___x_2946_, v___x_3015_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3092_ = lean_box(2);
v___x_3093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3091_);
lean_ctor_set(v___x_3093_, 2, v___x_3090_);
v___x_3094_ = l_Lean_Syntax_getArgs(v___x_3093_);
lean_dec_ref(v___x_3093_);
v_sz_3095_ = lean_array_size(v___x_3094_);
v___x_3096_ = ((size_t)0ULL);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_3095_, v___x_3096_, v___x_3094_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v___x_3098_; 
lean_dec(v___x_3052_);
v___x_3098_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2976_, v_a_2940_, v_a_2941_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3123_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
v_a_3100_ = lean_ctor_get(v___x_3098_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3102_ = v___x_3098_;
v_isShared_3103_ = v_isSharedCheck_3123_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_inc(v_a_3099_);
lean_dec(v___x_3098_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3123_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3104_ = 0;
v___x_3105_ = l_Lean_SourceInfo_fromRef(v_a_2940_, v___x_3104_);
v___x_3106_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3107_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3105_, 7);
v___x_3108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3105_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3105_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Lean_Syntax_node1(v___x_3105_, v___x_3091_, v___x_2966_);
v___x_3112_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3105_);
lean_ctor_set(v___x_3113_, 1, v___x_3091_);
lean_ctor_set(v___x_3113_, 2, v___x_3112_);
v___x_3114_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3105_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = l_Lean_Syntax_node5(v___x_3105_, v___x_2977_, v___x_3110_, v___x_3111_, v___x_3113_, v___x_3115_, v_a_3099_);
v___x_3117_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3105_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = l_Lean_Syntax_node3(v___x_3105_, v___x_3106_, v___x_3108_, v___x_3116_, v___x_3118_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3119_);
v___x_3121_ = v___x_3102_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_a_3100_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v___x_2966_);
v_a_3124_ = lean_ctor_get(v___x_3098_, 0);
v_a_3125_ = lean_ctor_get(v___x_3098_, 1);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3098_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_inc(v_a_3124_);
lean_dec(v___x_3098_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3124_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v_val_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_val_3133_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3133_);
lean_dec_ref(v___x_3097_);
v___x_3134_ = lean_unsigned_to_nat(2u);
v___x_3135_ = l_Lean_Syntax_getArg(v_00_u03a8_2976_, v___x_3134_);
v___x_3136_ = l_Lean_Syntax_matchesNull(v___x_3135_, v___x_2951_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
lean_dec(v_val_3133_);
lean_dec(v___x_3052_);
v___x_3137_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2976_, v_a_2940_, v_a_2941_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3161_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_a_3139_ = lean_ctor_get(v___x_3137_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3141_ = v___x_3137_;
v_isShared_3142_ = v_isSharedCheck_3161_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3161_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3143_ = l_Lean_SourceInfo_fromRef(v_a_2940_, v___x_3136_);
v___x_3144_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3145_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3143_, 7);
v___x_3146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3143_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3143_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = l_Lean_Syntax_node1(v___x_3143_, v___x_3091_, v___x_2966_);
v___x_3150_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3143_);
lean_ctor_set(v___x_3151_, 1, v___x_3091_);
lean_ctor_set(v___x_3151_, 2, v___x_3150_);
v___x_3152_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3143_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = l_Lean_Syntax_node5(v___x_3143_, v___x_2977_, v___x_3148_, v___x_3149_, v___x_3151_, v___x_3153_, v_a_3138_);
v___x_3155_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3143_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l_Lean_Syntax_node3(v___x_3143_, v___x_3144_, v___x_3146_, v___x_3154_, v___x_3156_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3157_);
v___x_3159_ = v___x_3141_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_a_3139_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v___x_2966_);
v_a_3162_ = lean_ctor_get(v___x_3137_, 0);
v_a_3163_ = lean_ctor_get(v___x_3137_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3137_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_inc(v_a_3162_);
lean_dec(v___x_3137_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3162_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v___x_3171_; lean_object* v_00_u03a8_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_unsigned_to_nat(4u);
v_00_u03a8_3172_ = l_Lean_Syntax_getArg(v_00_u03a8_2976_, v___x_3171_);
lean_dec(v_00_u03a8_2976_);
v___x_3173_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3172_, v_a_2940_, v_a_2941_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3202_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_a_3175_ = lean_ctor_get(v___x_3173_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3177_ = v___x_3173_;
v_isShared_3178_ = v_isSharedCheck_3202_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3202_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
uint8_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; size_t v_sz_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3179_ = 0;
v___x_3180_ = l_Lean_SourceInfo_fromRef(v_a_2940_, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3182_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3180_, 7);
v___x_3183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3180_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3180_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = l_Array_mkArray2___redArg(v___x_2966_, v___x_3052_);
v_sz_3187_ = lean_array_size(v_val_3133_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_3187_, v___x_3096_, v_val_3133_);
v___x_3189_ = l_Array_append___redArg(v___x_3186_, v___x_3188_);
lean_dec_ref(v___x_3188_);
v___x_3190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3180_);
lean_ctor_set(v___x_3190_, 1, v___x_3091_);
lean_ctor_set(v___x_3190_, 2, v___x_3189_);
v___x_3191_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3180_);
lean_ctor_set(v___x_3192_, 1, v___x_3091_);
lean_ctor_set(v___x_3192_, 2, v___x_3191_);
v___x_3193_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3180_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_Syntax_node5(v___x_3180_, v___x_2977_, v___x_3185_, v___x_3190_, v___x_3192_, v___x_3194_, v_a_3174_);
v___x_3196_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3180_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = l_Lean_Syntax_node3(v___x_3180_, v___x_3181_, v___x_3183_, v___x_3195_, v___x_3197_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3198_);
v___x_3200_ = v___x_3177_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_a_3175_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v_val_3133_);
lean_dec(v___x_3052_);
lean_dec(v___x_2966_);
v_a_3203_ = lean_ctor_get(v___x_3173_, 0);
v_a_3204_ = lean_ctor_get(v___x_3173_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3173_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_inc(v_a_3203_);
lean_dec(v___x_3173_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3203_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall___boxed(lean_object* v_x_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Std_Do_SPred_Notation_unexpandForall(v_x_3212_, v_a_3213_, v_a_3214_);
lean_dec(v_a_3213_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(lean_object* v___x_3220_, size_t v_sz_3221_, size_t v_i_3222_, lean_object* v_bs_3223_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_usize_dec_lt(v_i_3222_, v_sz_3221_);
if (v___x_3224_ == 0)
{
lean_dec(v___x_3220_);
return v_bs_3223_;
}
else
{
lean_object* v___x_3225_; lean_object* v_v_3226_; lean_object* v___x_3227_; lean_object* v_bs_x27_3228_; lean_object* v___x_3229_; size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_3226_ = lean_array_uget(v_bs_3223_, v_i_3222_);
v___x_3227_ = lean_unsigned_to_nat(0u);
v_bs_x27_3228_ = lean_array_uset(v_bs_3223_, v_i_3222_, v___x_3227_);
lean_inc(v___x_3220_);
v___x_3229_ = l_Lean_Syntax_node1(v___x_3220_, v___x_3225_, v_v_3226_);
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3222_, v___x_3230_);
v___x_3232_ = lean_array_uset(v_bs_x27_3228_, v_i_3222_, v___x_3229_);
v_i_3222_ = v___x_3231_;
v_bs_3223_ = v___x_3232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___boxed(lean_object* v___x_3234_, lean_object* v_sz_3235_, lean_object* v_i_3236_, lean_object* v_bs_3237_){
_start:
{
size_t v_sz_boxed_3238_; size_t v_i_boxed_3239_; lean_object* v_res_3240_; 
v_sz_boxed_3238_ = lean_unbox_usize(v_sz_3235_);
lean_dec(v_sz_3235_);
v_i_boxed_3239_ = lean_unbox_usize(v_i_3236_);
lean_dec(v_i_3236_);
v_res_3240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_3234_, v_sz_boxed_3238_, v_i_boxed_3239_, v_bs_3237_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(size_t v_sz_3241_, size_t v_i_3242_, lean_object* v_bs_3243_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3242_, v_sz_3241_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_bs_3243_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; lean_object* v_v_3247_; uint8_t v___x_3248_; 
v___x_3246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_3247_ = lean_array_uget_borrowed(v_bs_3243_, v_i_3242_);
lean_inc(v_v_3247_);
v___x_3248_ = l_Lean_Syntax_isOfKind(v_v_3247_, v___x_3246_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_dec_ref(v_bs_3243_);
v___x_3249_ = lean_box(0);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; lean_object* v_z_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
v___x_3250_ = lean_unsigned_to_nat(0u);
v_z_3251_ = l_Lean_Syntax_getArg(v_v_3247_, v___x_3250_);
v___x_3252_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_z_3251_);
v___x_3253_ = l_Lean_Syntax_isOfKind(v_z_3251_, v___x_3252_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; 
lean_dec(v_z_3251_);
lean_dec_ref(v_bs_3243_);
v___x_3254_ = lean_box(0);
return v___x_3254_;
}
else
{
lean_object* v_bs_x27_3255_; size_t v___x_3256_; size_t v___x_3257_; lean_object* v___x_3258_; 
v_bs_x27_3255_ = lean_array_uset(v_bs_3243_, v_i_3242_, v___x_3250_);
v___x_3256_ = ((size_t)1ULL);
v___x_3257_ = lean_usize_add(v_i_3242_, v___x_3256_);
v___x_3258_ = lean_array_uset(v_bs_x27_3255_, v_i_3242_, v_z_3251_);
v_i_3242_ = v___x_3257_;
v_bs_3243_ = v___x_3258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0___boxed(lean_object* v_sz_3260_, lean_object* v_i_3261_, lean_object* v_bs_3262_){
_start:
{
size_t v_sz_boxed_3263_; size_t v_i_boxed_3264_; lean_object* v_res_3265_; 
v_sz_boxed_3263_ = lean_unbox_usize(v_sz_3260_);
lean_dec(v_sz_3260_);
v_i_boxed_3264_ = lean_unbox_usize(v_i_3261_);
lean_dec(v_i_3261_);
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_boxed_3263_, v_i_boxed_3264_, v_bs_3262_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists(lean_object* v_x_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3271_);
v___x_3275_ = l_Lean_Syntax_isOfKind(v_x_3271_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec(v_x_3271_);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v_a_3273_);
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = l_Lean_Syntax_getArg(v_x_3271_, v___x_3278_);
lean_dec(v_x_3271_);
lean_inc(v___x_3279_);
v___x_3280_ = l_Lean_Syntax_matchesNull(v___x_3279_, v___x_3278_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec(v___x_3279_);
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v_a_3273_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = l_Lean_Syntax_getArg(v___x_3279_, v___x_3283_);
lean_dec(v___x_3279_);
v___x_3285_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_3284_);
v___x_3286_ = l_Lean_Syntax_isOfKind(v___x_3284_, v___x_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v_a_3273_);
return v___x_3288_;
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3289_ = l_Lean_Syntax_getArg(v___x_3284_, v___x_3278_);
lean_dec(v___x_3284_);
v___x_3290_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_3289_);
v___x_3291_ = l_Lean_Syntax_isOfKind(v___x_3289_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set(v___x_3293_, 1, v_a_3273_);
return v___x_3293_;
}
else
{
lean_object* v___x_3294_; uint8_t v___x_3295_; 
v___x_3294_ = l_Lean_Syntax_getArg(v___x_3289_, v___x_3283_);
lean_inc(v___x_3294_);
v___x_3295_ = l_Lean_Syntax_matchesNull(v___x_3294_, v___x_3278_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_dec(v___x_3294_);
lean_dec(v___x_3289_);
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v_a_3273_);
return v___x_3297_;
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3298_ = l_Lean_Syntax_getArg(v___x_3294_, v___x_3283_);
lean_dec(v___x_3294_);
v___x_3299_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_3298_);
v___x_3300_ = l_Lean_Syntax_isOfKind(v___x_3298_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec(v___x_3298_);
lean_dec(v___x_3289_);
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v_a_3273_);
return v___x_3302_;
}
else
{
lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = l_Lean_Syntax_getArg(v___x_3289_, v___x_3278_);
v___x_3304_ = l_Lean_Syntax_matchesNull(v___x_3303_, v___x_3283_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v___x_3298_);
lean_dec(v___x_3289_);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v_a_3273_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; lean_object* v_00_u03a8_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3307_ = lean_unsigned_to_nat(3u);
v_00_u03a8_3308_ = l_Lean_Syntax_getArg(v___x_3289_, v___x_3307_);
lean_dec(v___x_3289_);
v___x_3309_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11));
lean_inc(v_00_u03a8_3308_);
v___x_3310_ = l_Lean_Syntax_isOfKind(v_00_u03a8_3308_, v___x_3309_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3342_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_a_3313_ = lean_ctor_get(v___x_3311_, 1);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3315_ = v___x_3311_;
v_isShared_3316_ = v_isSharedCheck_3342_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3342_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3317_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3310_);
v___x_3318_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3319_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3317_, 10);
v___x_3320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3317_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3317_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
v___x_3324_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_3325_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3327_ = l_Lean_Syntax_node1(v___x_3317_, v___x_3326_, v___x_3298_);
v___x_3328_ = l_Lean_Syntax_node1(v___x_3317_, v___x_3325_, v___x_3327_);
v___x_3329_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3317_);
lean_ctor_set(v___x_3330_, 1, v___x_3325_);
lean_ctor_set(v___x_3330_, 2, v___x_3329_);
v___x_3331_ = l_Lean_Syntax_node2(v___x_3317_, v___x_3324_, v___x_3328_, v___x_3330_);
v___x_3332_ = l_Lean_Syntax_node1(v___x_3317_, v___x_3323_, v___x_3331_);
v___x_3333_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3317_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = l_Lean_Syntax_node4(v___x_3317_, v___x_3309_, v___x_3322_, v___x_3332_, v___x_3334_, v_a_3312_);
v___x_3336_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3317_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = l_Lean_Syntax_node3(v___x_3317_, v___x_3318_, v___x_3320_, v___x_3335_, v___x_3337_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v___x_3338_);
v___x_3340_ = v___x_3315_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_a_3313_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v___x_3298_);
v_a_3343_ = lean_ctor_get(v___x_3311_, 0);
v_a_3344_ = lean_ctor_get(v___x_3311_, 1);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3311_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_inc(v_a_3343_);
lean_dec(v___x_3311_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3343_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3352_ = l_Lean_Syntax_getArg(v_00_u03a8_3308_, v___x_3278_);
v___x_3353_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
lean_inc(v___x_3352_);
v___x_3354_ = l_Lean_Syntax_isOfKind(v___x_3352_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v___x_3352_);
v___x_3355_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3385_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_a_3357_ = lean_ctor_get(v___x_3355_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3359_ = v___x_3355_;
v_isShared_3360_ = v_isSharedCheck_3385_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3385_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3361_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3354_);
v___x_3362_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3363_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3361_, 10);
v___x_3364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3361_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3361_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_3368_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3370_ = l_Lean_Syntax_node1(v___x_3361_, v___x_3369_, v___x_3298_);
v___x_3371_ = l_Lean_Syntax_node1(v___x_3361_, v___x_3368_, v___x_3370_);
v___x_3372_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3361_);
lean_ctor_set(v___x_3373_, 1, v___x_3368_);
lean_ctor_set(v___x_3373_, 2, v___x_3372_);
v___x_3374_ = l_Lean_Syntax_node2(v___x_3361_, v___x_3367_, v___x_3371_, v___x_3373_);
v___x_3375_ = l_Lean_Syntax_node1(v___x_3361_, v___x_3353_, v___x_3374_);
v___x_3376_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3361_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_Syntax_node4(v___x_3361_, v___x_3309_, v___x_3366_, v___x_3375_, v___x_3377_, v_a_3356_);
v___x_3379_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3361_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_Lean_Syntax_node3(v___x_3361_, v___x_3362_, v___x_3364_, v___x_3378_, v___x_3380_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3381_);
v___x_3383_ = v___x_3359_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_a_3357_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v___x_3298_);
v_a_3386_ = lean_ctor_get(v___x_3355_, 0);
v_a_3387_ = lean_ctor_get(v___x_3355_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3355_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_inc(v_a_3386_);
lean_dec(v___x_3355_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3386_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = l_Lean_Syntax_getArg(v___x_3352_, v___x_3283_);
lean_dec(v___x_3352_);
v___x_3396_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
lean_inc(v___x_3395_);
v___x_3397_ = l_Lean_Syntax_isOfKind(v___x_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_dec(v___x_3395_);
v___x_3398_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3427_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_a_3400_ = lean_ctor_get(v___x_3398_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3402_ = v___x_3398_;
v_isShared_3403_ = v_isSharedCheck_3427_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3427_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3404_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3397_);
v___x_3405_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3406_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3404_, 10);
v___x_3407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3404_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3404_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3412_ = l_Lean_Syntax_node1(v___x_3404_, v___x_3411_, v___x_3298_);
v___x_3413_ = l_Lean_Syntax_node1(v___x_3404_, v___x_3410_, v___x_3412_);
v___x_3414_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3404_);
lean_ctor_set(v___x_3415_, 1, v___x_3410_);
lean_ctor_set(v___x_3415_, 2, v___x_3414_);
v___x_3416_ = l_Lean_Syntax_node2(v___x_3404_, v___x_3396_, v___x_3413_, v___x_3415_);
v___x_3417_ = l_Lean_Syntax_node1(v___x_3404_, v___x_3353_, v___x_3416_);
v___x_3418_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3419_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3404_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = l_Lean_Syntax_node4(v___x_3404_, v___x_3309_, v___x_3409_, v___x_3417_, v___x_3419_, v_a_3399_);
v___x_3421_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3404_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = l_Lean_Syntax_node3(v___x_3404_, v___x_3405_, v___x_3407_, v___x_3420_, v___x_3422_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v___x_3423_);
v___x_3425_ = v___x_3402_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_a_3400_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v___x_3298_);
v_a_3428_ = lean_ctor_get(v___x_3398_, 0);
v_a_3429_ = lean_ctor_get(v___x_3398_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3398_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_inc(v_a_3428_);
lean_dec(v___x_3398_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3428_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3437_ = l_Lean_Syntax_getArg(v___x_3395_, v___x_3283_);
v___x_3438_ = l_Lean_Syntax_getNumArgs(v___x_3437_);
v___x_3439_ = lean_nat_dec_le(v___x_3278_, v___x_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
lean_dec(v___x_3438_);
lean_dec(v___x_3437_);
lean_dec(v___x_3395_);
v___x_3440_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3469_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_a_3442_ = lean_ctor_get(v___x_3440_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3444_ = v___x_3440_;
v_isShared_3445_ = v_isSharedCheck_3469_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3469_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3446_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3439_);
v___x_3447_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3448_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3446_, 10);
v___x_3449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3446_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3446_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3454_ = l_Lean_Syntax_node1(v___x_3446_, v___x_3453_, v___x_3298_);
v___x_3455_ = l_Lean_Syntax_node1(v___x_3446_, v___x_3452_, v___x_3454_);
v___x_3456_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3446_);
lean_ctor_set(v___x_3457_, 1, v___x_3452_);
lean_ctor_set(v___x_3457_, 2, v___x_3456_);
v___x_3458_ = l_Lean_Syntax_node2(v___x_3446_, v___x_3396_, v___x_3455_, v___x_3457_);
v___x_3459_ = l_Lean_Syntax_node1(v___x_3446_, v___x_3353_, v___x_3458_);
v___x_3460_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3446_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = l_Lean_Syntax_node4(v___x_3446_, v___x_3309_, v___x_3451_, v___x_3459_, v___x_3461_, v_a_3441_);
v___x_3463_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3446_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = l_Lean_Syntax_node3(v___x_3446_, v___x_3447_, v___x_3449_, v___x_3462_, v___x_3464_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3465_);
v___x_3467_ = v___x_3444_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_a_3442_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v___x_3298_);
v_a_3470_ = lean_ctor_get(v___x_3440_, 0);
v_a_3471_ = lean_ctor_get(v___x_3440_, 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3440_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_inc(v_a_3470_);
lean_dec(v___x_3440_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3470_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = l_Lean_Syntax_getArg(v___x_3437_, v___x_3283_);
v___x_3480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_3479_);
v___x_3481_ = l_Lean_Syntax_isOfKind(v___x_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
lean_dec(v___x_3479_);
lean_dec(v___x_3438_);
lean_dec(v___x_3437_);
lean_dec(v___x_3395_);
v___x_3482_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3510_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_a_3484_ = lean_ctor_get(v___x_3482_, 1);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3486_ = v___x_3482_;
v_isShared_3487_ = v_isSharedCheck_3510_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3510_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3488_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3481_);
v___x_3489_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3490_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3488_, 10);
v___x_3491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3488_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3488_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3495_ = l_Lean_Syntax_node1(v___x_3488_, v___x_3480_, v___x_3298_);
v___x_3496_ = l_Lean_Syntax_node1(v___x_3488_, v___x_3494_, v___x_3495_);
v___x_3497_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3488_);
lean_ctor_set(v___x_3498_, 1, v___x_3494_);
lean_ctor_set(v___x_3498_, 2, v___x_3497_);
v___x_3499_ = l_Lean_Syntax_node2(v___x_3488_, v___x_3396_, v___x_3496_, v___x_3498_);
v___x_3500_ = l_Lean_Syntax_node1(v___x_3488_, v___x_3353_, v___x_3499_);
v___x_3501_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3488_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_Syntax_node4(v___x_3488_, v___x_3309_, v___x_3493_, v___x_3500_, v___x_3502_, v_a_3483_);
v___x_3504_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3488_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = l_Lean_Syntax_node3(v___x_3488_, v___x_3489_, v___x_3491_, v___x_3503_, v___x_3505_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3506_);
v___x_3508_ = v___x_3486_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_a_3484_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v___x_3298_);
v_a_3511_ = lean_ctor_get(v___x_3482_, 0);
v_a_3512_ = lean_ctor_get(v___x_3482_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3482_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_inc(v_a_3511_);
lean_dec(v___x_3482_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3511_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3520_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3283_);
lean_dec(v___x_3479_);
lean_inc(v___x_3520_);
v___x_3521_ = l_Lean_Syntax_isOfKind(v___x_3520_, v___x_3299_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_dec(v___x_3520_);
lean_dec(v___x_3438_);
lean_dec(v___x_3437_);
lean_dec(v___x_3395_);
v___x_3522_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3550_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_a_3524_ = lean_ctor_get(v___x_3522_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3526_ = v___x_3522_;
v_isShared_3527_ = v_isSharedCheck_3550_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3550_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3528_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3521_);
v___x_3529_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3530_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3528_, 10);
v___x_3531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3528_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3528_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3535_ = l_Lean_Syntax_node1(v___x_3528_, v___x_3480_, v___x_3298_);
v___x_3536_ = l_Lean_Syntax_node1(v___x_3528_, v___x_3534_, v___x_3535_);
v___x_3537_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3528_);
lean_ctor_set(v___x_3538_, 1, v___x_3534_);
lean_ctor_set(v___x_3538_, 2, v___x_3537_);
v___x_3539_ = l_Lean_Syntax_node2(v___x_3528_, v___x_3396_, v___x_3536_, v___x_3538_);
v___x_3540_ = l_Lean_Syntax_node1(v___x_3528_, v___x_3353_, v___x_3539_);
v___x_3541_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3528_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = l_Lean_Syntax_node4(v___x_3528_, v___x_3309_, v___x_3533_, v___x_3540_, v___x_3542_, v_a_3523_);
v___x_3544_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3528_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = l_Lean_Syntax_node3(v___x_3528_, v___x_3529_, v___x_3531_, v___x_3543_, v___x_3545_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3546_);
v___x_3548_ = v___x_3526_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_a_3524_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec(v___x_3298_);
v_a_3551_ = lean_ctor_get(v___x_3522_, 0);
v_a_3552_ = lean_ctor_get(v___x_3522_, 1);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3522_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_inc(v_a_3551_);
lean_dec(v___x_3522_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3551_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; size_t v_sz_3566_; size_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3560_ = l_Lean_Syntax_getArgs(v___x_3437_);
lean_dec(v___x_3437_);
v___x_3561_ = l_Array_extract___redArg(v___x_3560_, v___x_3278_, v___x_3438_);
lean_dec_ref(v___x_3560_);
v___x_3562_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3563_ = lean_box(2);
v___x_3564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3562_);
lean_ctor_set(v___x_3564_, 2, v___x_3561_);
v___x_3565_ = l_Lean_Syntax_getArgs(v___x_3564_);
lean_dec_ref(v___x_3564_);
v_sz_3566_ = lean_array_size(v___x_3565_);
v___x_3567_ = ((size_t)0ULL);
v___x_3568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_3566_, v___x_3567_, v___x_3565_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v___x_3569_; 
lean_dec(v___x_3520_);
lean_dec(v___x_3395_);
v___x_3569_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3597_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_a_3571_ = lean_ctor_get(v___x_3569_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3573_ = v___x_3569_;
v_isShared_3574_ = v_isSharedCheck_3597_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3597_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3575_ = 0;
v___x_3576_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3575_);
v___x_3577_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3578_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3576_, 10);
v___x_3579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3576_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3576_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = l_Lean_Syntax_node1(v___x_3576_, v___x_3480_, v___x_3298_);
v___x_3583_ = l_Lean_Syntax_node1(v___x_3576_, v___x_3562_, v___x_3582_);
v___x_3584_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3576_);
lean_ctor_set(v___x_3585_, 1, v___x_3562_);
lean_ctor_set(v___x_3585_, 2, v___x_3584_);
v___x_3586_ = l_Lean_Syntax_node2(v___x_3576_, v___x_3396_, v___x_3583_, v___x_3585_);
v___x_3587_ = l_Lean_Syntax_node1(v___x_3576_, v___x_3353_, v___x_3586_);
v___x_3588_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3576_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Lean_Syntax_node4(v___x_3576_, v___x_3309_, v___x_3581_, v___x_3587_, v___x_3589_, v_a_3570_);
v___x_3591_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3576_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = l_Lean_Syntax_node3(v___x_3576_, v___x_3577_, v___x_3579_, v___x_3590_, v___x_3592_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3593_);
v___x_3595_ = v___x_3573_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_a_3571_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v___x_3298_);
v_a_3598_ = lean_ctor_get(v___x_3569_, 0);
v_a_3599_ = lean_ctor_get(v___x_3569_, 1);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3569_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_inc(v_a_3598_);
lean_dec(v___x_3569_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3598_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v_val_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v_val_3607_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_val_3607_);
lean_dec_ref(v___x_3568_);
v___x_3608_ = l_Lean_Syntax_getArg(v___x_3395_, v___x_3278_);
lean_dec(v___x_3395_);
v___x_3609_ = l_Lean_Syntax_matchesNull(v___x_3608_, v___x_3283_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec(v_val_3607_);
lean_dec(v___x_3520_);
v___x_3610_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3308_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3637_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_a_3612_ = lean_ctor_get(v___x_3610_, 1);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3614_ = v___x_3610_;
v_isShared_3615_ = v_isSharedCheck_3637_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3637_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3616_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3609_);
v___x_3617_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3618_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3616_, 10);
v___x_3619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3616_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3616_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = l_Lean_Syntax_node1(v___x_3616_, v___x_3480_, v___x_3298_);
v___x_3623_ = l_Lean_Syntax_node1(v___x_3616_, v___x_3562_, v___x_3622_);
v___x_3624_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3616_);
lean_ctor_set(v___x_3625_, 1, v___x_3562_);
lean_ctor_set(v___x_3625_, 2, v___x_3624_);
v___x_3626_ = l_Lean_Syntax_node2(v___x_3616_, v___x_3396_, v___x_3623_, v___x_3625_);
v___x_3627_ = l_Lean_Syntax_node1(v___x_3616_, v___x_3353_, v___x_3626_);
v___x_3628_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3616_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = l_Lean_Syntax_node4(v___x_3616_, v___x_3309_, v___x_3621_, v___x_3627_, v___x_3629_, v_a_3611_);
v___x_3631_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3616_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = l_Lean_Syntax_node3(v___x_3616_, v___x_3617_, v___x_3619_, v___x_3630_, v___x_3632_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3633_);
v___x_3635_ = v___x_3614_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_a_3612_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec(v___x_3298_);
v_a_3638_ = lean_ctor_get(v___x_3610_, 0);
v_a_3639_ = lean_ctor_get(v___x_3610_, 1);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3610_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_inc(v_a_3638_);
lean_dec(v___x_3610_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3638_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
else
{
lean_object* v_00_u03a8_3647_; lean_object* v___x_3648_; 
v_00_u03a8_3647_ = l_Lean_Syntax_getArg(v_00_u03a8_3308_, v___x_3307_);
lean_dec(v_00_u03a8_3308_);
v___x_3648_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3647_, v_a_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3681_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_a_3650_ = lean_ctor_get(v___x_3648_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3652_ = v___x_3648_;
v_isShared_3653_ = v_isSharedCheck_3681_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3681_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
uint8_t v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; size_t v_sz_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3654_ = 0;
v___x_3655_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3654_);
v___x_3656_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3657_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3655_, 12);
v___x_3658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3655_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3655_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_Lean_Syntax_node1(v___x_3655_, v___x_3480_, v___x_3298_);
v___x_3662_ = l_Lean_Syntax_node1(v___x_3655_, v___x_3480_, v___x_3520_);
v___x_3663_ = l_Array_mkArray2___redArg(v___x_3661_, v___x_3662_);
v_sz_3664_ = lean_array_size(v_val_3607_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_3655_, v_sz_3664_, v___x_3567_, v_val_3607_);
v___x_3666_ = l_Array_append___redArg(v___x_3663_, v___x_3665_);
lean_dec_ref(v___x_3665_);
v___x_3667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3655_);
lean_ctor_set(v___x_3667_, 1, v___x_3562_);
lean_ctor_set(v___x_3667_, 2, v___x_3666_);
v___x_3668_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3655_);
lean_ctor_set(v___x_3669_, 1, v___x_3562_);
lean_ctor_set(v___x_3669_, 2, v___x_3668_);
v___x_3670_ = l_Lean_Syntax_node2(v___x_3655_, v___x_3396_, v___x_3667_, v___x_3669_);
v___x_3671_ = l_Lean_Syntax_node1(v___x_3655_, v___x_3353_, v___x_3670_);
v___x_3672_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3655_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = l_Lean_Syntax_node4(v___x_3655_, v___x_3309_, v___x_3660_, v___x_3671_, v___x_3673_, v_a_3649_);
v___x_3675_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3655_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Lean_Syntax_node3(v___x_3655_, v___x_3656_, v___x_3658_, v___x_3674_, v___x_3676_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3677_);
v___x_3679_ = v___x_3652_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_a_3650_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_val_3607_);
lean_dec(v___x_3520_);
lean_dec(v___x_3298_);
v_a_3682_ = lean_ctor_get(v___x_3648_, 0);
v_a_3683_ = lean_ctor_get(v___x_3648_, 1);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3648_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_inc(v_a_3682_);
lean_dec(v___x_3648_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3682_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists___boxed(lean_object* v_x_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Std_Do_SPred_Notation_unexpandExists(v_x_3691_, v_a_3692_, v_a_3693_);
lean_dec(v_a_3692_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff(lean_object* v_x_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3699_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3696_);
v___x_3700_ = l_Lean_Syntax_isOfKind(v_x_3696_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_dec(v_x_3696_);
v___x_3701_ = lean_box(0);
v___x_3702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_ctor_set(v___x_3702_, 1, v_a_3698_);
return v___x_3702_;
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3703_ = lean_unsigned_to_nat(1u);
v___x_3704_ = l_Lean_Syntax_getArg(v_x_3696_, v___x_3703_);
lean_dec(v_x_3696_);
v___x_3705_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3704_);
v___x_3706_ = l_Lean_Syntax_matchesNull(v___x_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
lean_dec(v___x_3704_);
v___x_3707_ = lean_box(0);
v___x_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
lean_ctor_set(v___x_3708_, 1, v_a_3698_);
return v___x_3708_;
}
else
{
lean_object* v___x_3709_; lean_object* v_P_3710_; lean_object* v___x_3711_; 
v___x_3709_ = lean_unsigned_to_nat(0u);
v_P_3710_ = l_Lean_Syntax_getArg(v___x_3704_, v___x_3709_);
v___x_3711_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_3710_, v_a_3697_, v_a_3698_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v_a_3713_; lean_object* v_Q_3714_; lean_object* v___x_3715_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
v_a_3713_ = lean_ctor_get(v___x_3711_, 1);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3711_);
v_Q_3714_ = l_Lean_Syntax_getArg(v___x_3704_, v___x_3703_);
lean_dec(v___x_3704_);
v___x_3715_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_3714_, v_a_3697_, v_a_3713_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3736_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
v_a_3717_ = lean_ctor_get(v___x_3715_, 1);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3719_ = v___x_3715_;
v_isShared_3720_ = v_isSharedCheck_3736_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_inc(v_a_3716_);
lean_dec(v___x_3715_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3736_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
uint8_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
v___x_3721_ = 0;
v___x_3722_ = l_Lean_SourceInfo_fromRef(v_a_3697_, v___x_3721_);
v___x_3723_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3724_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3722_, 4);
v___x_3725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3722_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9));
v___x_3727_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandIff___closed__0));
v___x_3728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3722_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = l_Lean_Syntax_node3(v___x_3722_, v___x_3726_, v_a_3712_, v___x_3728_, v_a_3716_);
v___x_3730_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3722_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = l_Lean_Syntax_node3(v___x_3722_, v___x_3723_, v___x_3725_, v___x_3729_, v___x_3731_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3732_);
v___x_3734_ = v___x_3719_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_a_3717_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3712_);
v_a_3737_ = lean_ctor_get(v___x_3715_, 0);
v_a_3738_ = lean_ctor_get(v___x_3715_, 1);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3715_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_inc(v_a_3737_);
lean_dec(v___x_3715_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3737_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v___x_3704_);
v_a_3746_ = lean_ctor_get(v___x_3711_, 0);
v_a_3747_ = lean_ctor_get(v___x_3711_, 1);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3711_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_inc(v_a_3746_);
lean_dec(v___x_3711_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3746_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff___boxed(lean_object* v_x_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Std_Do_SPred_Notation_unexpandIff(v_x_3755_, v_a_3756_, v_a_3757_);
lean_dec(v_a_3756_);
return v_res_3758_;
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
